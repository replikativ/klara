(ns klara.compile.ir
  "K0 -> named K1 with operation-class evidence. Obligation: preserve
  binding, evaluation order and handler extent. Unknown operations remain
  :general and prevent emission; declarations alone are not evidence."
  (:require [klara.core :as c]
            [klara.compile.runtime :as runtime]))

(defn map-children [f t]
  (case (:op t)
    (:local :quote :resolve) t
    :fn (update t :body f)
    (:app :specialize) (-> t (update :fn f) (update :args #(mapv f %)))
    :let (-> t (update :init f) (update :body f))
    :if (-> t (update :test f) (update :then f) (update :else f))
    :letrec (-> t (update :inits #(mapv f %)) (update :body f))
    :prim (update t :args #(mapv f %))
    :perform (cond-> (update t :args #(mapv f %)) (:target t) (update :target f))
    :handle (cond-> (-> t (update :clauses #(update-vals % f)) (update :body f))
              (:return t) (update :return f))
    (:code :esc) t))

(defn nodes [t] (tree-seq #(seq (c/children %)) c/children t))
(defn uses [t s] (count (filter #(and (= :local (:op %)) (= s (:name %))) (nodes t))))
(defn substitute [t env]
  (if (= :local (:op t)) (get env (:name t) t)
      (map-children #(substitute % env) t)))
(defn trivial? [t] (contains? #{:quote :local} (:op t)))

(defn named
  "Fresh names eliminate capture during substitution. Quoted data is opaque."
  ([t] (named t []))
  ([t env]
   (let [go #(named % env) fresh #(vec (repeatedly % (fn [] (gensym "v"))))]
     (case (:op t)
       :local {:op :local :name (nth env (- (count env) 1 (:index t)))}
       :fn (let [ps (fresh (+ (:arity t) (if (:rest? t) 1 0)))]
             (assoc t :params ps :body (named (:body t) (into env ps))))
       :let (let [s (gensym "v")]
              (assoc t :name s :init (go (:init t)) :body (named (:body t) (conj env s))))
       :letrec (let [ss (fresh (count (:inits t))) e (into env ss)]
                 (assoc t :names ss :inits (mapv #(named % e) (:inits t)) :body (named (:body t) e)))
       :handle (let [s (gensym "handler")]
                 (assoc t :name s :clauses (update-vals (:clauses t) go)
                        :return (some-> (:return t) go) :body (named (:body t) (conj env s))))
       (map-children go t)))))

(defn clause-class [t]
  (if (and (= :fn (:op t)) (not (:rest? t)) (pos? (:arity t)))
    (let [k (peek (:params t)) b (:body t)]
      (cond
        (zero? (uses b k)) :abortive
        (and (= :app (:op b)) (= {:op :local :name k} (:fn b))
             (= 1 (count (:args b))) (= 1 (uses b k))) :tail-resumptive
        :else :general))
    :general))

(defn lower [t]
  (letfn [(go [t handlers]
            (if (= :handle (:op t))
              (let [classes (update-vals (:clauses t) clause-class)]
                (assoc (map-children #(go % handlers) t)
                       :classes classes
                       :body (go (:body t) (assoc handlers (:name t) classes))))
              (let [t (map-children #(go % handlers) t)]
                (if (= :perform (:op t))
                  (assoc t :class (if (and (nil? (:target t)) (runtime/authority-ops (:name t)))
                                    :tail-resumptive
                                    (get-in handlers [(get-in t [:target :name]) (:name t)] :general))) t))))]
    (go t {})))
