(ns klara.compile.anf
  "A-normal form for lowering (L4.exec.frame-state).

  Every argument of a call, test of an `if`, thrown value and recur argument
  that is not trivial is bound by a `let`, left to right. Afterwards every
  point where compiled code may leave is a let initializer or a tail
  position, so every enclosing context is a `let` frame the interpreter
  already knows. Bindings are introduced in evaluation order, so the
  normalization preserves meaning (L4.check.let-app); `do` becomes a chain of
  lets."
  (:require [klara.lang.term :as t]))

(set! *warn-on-reflection* true)

(defn trivial?
  "Terms whose evaluation cannot fail, perform an effect or leave."
  [term]
  (contains? #{:const :local :global :host} (:op term)))

(declare anf)

(defn- bind-all
  "Normalize `terms` in order; returns [bindings trivial-terms]."
  [terms]
  (reduce (fn [[bs out] x]
            (let [x (anf x)]
              (if (or (trivial? x) (= :fn (:op x)))
                [bs (conj out x)]
                (let [n (t/fresh "a")] [(conj bs [n x]) (conj out (t/local n))]))))
          [[] []] terms))

(defn- wrap [bindings body]
  (reduce (fn [b [n init]] (t/let1 n init b)) body (rseq bindings)))

(defn anf
  "The A-normal form of `term`."
  [term]
  (case (:op term)
    (:const :local :global :host :hole) term
    :fn (t/fn-term (:self term) (mapv #(update % :body anf) (:arities term)))
    :app (let [[bs [f & args]] (bind-all (cons (:fn term) (:args term)))]
           (wrap bs (assoc term :fn f :args (vec args))))
    :recur (let [[bs args] (bind-all (:args term))]
             (wrap bs (assoc term :args args)))
    :let (assoc term :init (anf (:init term)) :body (anf (:body term)))
    :if (let [[bs [test]] (bind-all [(:test term)])]
          (wrap bs (assoc term :test test :then (anf (:then term)) :else (anf (:else term)))))
    :do (let [[x & more] (:body term)]
          (if more
            (t/let1 (t/fresh "do") (anf x) (anf (t/do* (vec more))))
            (anf x)))
    :throw (let [[bs [ex]] (bind-all [(:ex term)])]
             (wrap bs (assoc term :ex ex)))
    ;; outside the compilable subset; lowering rejects them
    term))
