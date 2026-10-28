(ns klara.compile.speculate
  "A deliberately small source-position preserving speculation pass.
  Checkpoint only a binary + with a trivial first operand after a let spine.
  There are no pending generic frames there. Other control/allocations
  decline speculation; the ordinary compiler still handles them."
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
                t))]
      (let [ps (:params term)
            slots (mapv #(slot {:op :local :name %}) ps)
            body (go (:body term) [:body] slots (zipmap ps (range)) 0)]
        ;; Do not retain field-capture transformations if no checkpoint exists.
        {:term (if (seq @states) (assoc term :body body) term) :frame-states @states}))))
