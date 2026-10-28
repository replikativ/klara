(ns klara.compile.speculate
  "A deliberately small source-position preserving speculation pass.
  Checkpoint a binary + after a let spine, or the head of a single
  self-tail loop in that spine. Neither position has pending generic
  frames. Other control/allocations decline speculation."
  (:require [klara.compile.ir :as ir]))

(defn run [term code-id]
  (let [states (atom []) live (atom [])
        slot (fn [t] (let [i (count @live)] (swap! live conj t) [:live i]))]
    (letfn [(go [t path slots names depth]
              (case (:op t)
                :let
                (let [init (:init t) s (:name t) p (conj path :init)
                      ;; Field evaluation is bound once, in order, even when a
                      ;; later projection or the allocation itself disappears.
                      fields (when (and (= :prim (:op init)) (= 'vector (:name init)))
                               (mapv (fn [a] [(gensym "livefield") a]) (:args init)))
                      virtual (cond
                                (= :fn (:op init)) [:closure p]
                                fields [:vector (mapv (fn [[s _]] (slot {:op :local :name s})) fields)]
                                (= :local (:op init)) (when-let [i (get names (:name init))] [:local i]))]
                  (if (and (= :prim (:op init)) (contains? '#{hash-map list hash-set} (:name init)))
                    t
                    (let [desc (or virtual (slot {:op :local :name s}))
                          body (go (:body t) (conj path :body) (conj slots desc)
                                   (assoc names s (count slots)) (inc depth))
                          t (assoc t :body body :init (if fields
                                                      (assoc init :args (mapv (fn [[s _]] {:op :local :name s}) fields)) init))]
                      (reduce (fn [b [s a]] {:op :let :name s :init a :body b}) t (reverse fields)))))
                :prim
                (if (and (pos? depth) (= '+ (:name t)) (= 2 (count (:args t)))
                         (ir/trivial? (first (:args t))))
                  (do (reset! states [{:site path :at [:eval path] :env slots :kont []}])
                      {:op :numeric-guard :args (:args t) :live @live :code-id code-id :site path}) t)
                :letrec
                (let [f (first (:inits t)) s (first (:names t)) b (:body t)
                      p (conj path :inits 0 :body)]
                  (if (and (= 1 (count (:inits t))) (not (:rest? f))
                           (= :app (:op b)) (= {:op :local :name s} (:fn b))
                           (= (:arity f) (count (:args b)))
                           (not-any? #(contains? #{:handle :perform :fn :letrec} (:op %))
                                     (ir/nodes (:body f)))
                           (some #(and (= :prim (:op %))
                                       (contains? '#{+ - * / inc dec} (:name %))) (ir/nodes (:body f))))
                    (let [params (mapv #(hash-map :op :local :name %) (:params f))
                          env (into (conj slots [:letrec path 0]) (mapv slot params))]
                      (reset! states [{:site p :at [:eval p] :env env :kont []}])
                      (assoc-in t [:inits 0 :body]
                                {:op :loop-check :args params :body (:body f)
                                 :live @live :code-id code-id :site p}))
                    t))
                t))]
      (let [ps (:params term)
            slots (mapv #(slot {:op :local :name %}) ps)
            body (go (:body term) [:body] slots (zipmap ps (range)) 0)]
        ;; Do not retain field-capture transformations if no checkpoint exists.
        {:term (if (seq @states) (assoc term :body body) term) :frame-states @states}))))
