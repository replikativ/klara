(ns klara.compile.unbox
  "Closed numeric loop facts. Runtime class guards license initial values;
  this small abstract interpreter proves every backedge preserves the class.
  Unknown carried layouts, promotion and division decline the layout. A generic
  comparison may establish Boolean without establishing its operand layouts.
  Checked Clojure arithmetic remains checked; no algebraic rewriting."
  (:require [klara.compile.loop :as loop]))

(def arithmetic '#{+ - * inc dec})
(def comparisons '#{< > <= >= = not= zero? pos? neg?})

(defn scalar-kind [t env]
  ;; A total, effect-free fragment. Unknown forms never establish a return
  ;; contract, even when feedback has observed only longs so far.
  (case (:op t)
    :quote (cond (instance? Long (:datum t)) :long
                 (instance? Double (:datum t)) :double
                 (instance? Boolean (:datum t)) :boolean)
    :local (get env (:name t))
    :let (when-let [k (scalar-kind (:init t) env)]
           (scalar-kind (:body t) (assoc env (:name t) k)))
    :if (when (= :boolean (scalar-kind (:test t) env))
          (let [a (scalar-kind (:then t) env)
                b (scalar-kind (:else t) env)]
            (when (= a b) a)))
    :prim (let [ks (mapv #(scalar-kind % env) (:args t))]
            (when (and (seq ks) (every? #{:long :double} ks))
              (cond (arithmetic (:name t)) (if (some #{:double} ks) :double :long)
                    (comparisons (:name t)) :boolean)))
    nil))

(defn return-layout [term]
  (when (and (= :fn (:op term)) (not (:rest? term))
             (pos? (:arity term)))
    (let [k (scalar-kind (:body term)
                         (zipmap (:params term) (repeat :long)))]
      (when (= :long k) {:args (vec (repeat (:arity term) :long))
                       :return :long}))))

(defn invariant?
  [f recursive kind summaries]
  (let [facts (zipmap (:params f) (repeat kind))]
    (letfn [(infer [t env]
              (case (:op t)
                :quote (cond (instance? Long (:datum t)) :long
                             (instance? Double (:datum t)) :double
                             (boolean? (:datum t)) :boolean)
                :local (get env (:name t))
                :loop-check (infer (:body t) env)
                :let (when-let [k (infer (:init t) env)]
                       (infer (:body t) (assoc env (:name t) k)))
                :if (when (infer (:test t) env)
                      (let [a (infer (:then t) env) b (infer (:else t) env)]
                        (when (and a b) (if (= a :recur) b (if (= b :recur) a (when (= a b) a))))))
                :prim (let [ks (mapv #(infer % env) (:args t)) n (:name t)]
                        (when (seq ks)
                          (cond
                            ;; A comparison returns Boolean on normal completion,
                            ;; even when an operand layout is unknown. Its emitted
                            ;; evaluation stays generic and can still throw.
                            (comparisons n) :boolean
                            (and (arithmetic n) (every? #{:long :double} ks))
                            (if (some #{:double} ks) :double :long))))
                :app (cond
                       (and (= {:op :local :name recursive} (:fn t))
                            (= (count (:params f)) (count (:args t)))
                            (every? #(= kind (infer % env)) (:args t))) :recur
                       (= :resolve (get-in t [:fn :op]))
                       (let [{:keys [args return]} (get summaries (get-in t [:fn :id]))]
                         (when (and (= kind return)
                                    (= args (mapv #(infer % env) (:args t)))) return)))
                nil))]
      (boolean (infer (:body f) facts)))))

(defn loop-kinds [t summaries]
  (when-let [{:keys [self function entry]} (loop/view t)]
    (filterv (fn [kind]
               (and (every? #(or (not= :quote (:op %))
                                (if (= kind :long) (instance? Long (:datum %))
                                    (instance? Double (:datum %)))) (get-in entry [:node :args]))
                    (invariant? function self kind summaries))) [:long :double])))
