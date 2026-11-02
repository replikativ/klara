(ns klara.compile.fusion
  "Fold fusion as a law-licensed rewrite (L4.check.law, design/05-specialization.md).

  `fuse` recognizes a function whose body folds a chain of `map` and
  `filter` stages over its parameter,

    (fn [xs] (reduce f init (map g (filter p .. xs))))

  and builds the one-pass loop the fusion laws equate it with (Law.foldl-map
  and Law.foldl-filter, proved in spec/formal/src/klara/formal/laws.clj):

    (fn [xs] (try (loop over xs: acc := (f acc (g x)) where (p x) ..,
                   stopping on reduced, as reduce does)
                  (catch Throwable e (reduce f init (map g (filter p .. xs))))))

  Stages stay calls, so a stage's own compiled code (say a certified one)
  runs inside the fused loop. Any exception makes the loop give way to the
  reference body, so the error observed is the reference's: Clojure's lazy
  stages are chunked, and the loop's interleaved order would otherwise raise
  a different error first. This is sound because the stages are pure
  (the certifier's premises) and the argument is a vector (its guard).

  The recipe (`klara.jit/fuse`) calls `fuse`; the certifier calls it again
  on the reference and compares, so a recipe that builds anything else is
  rejected."
  (:require [klara.lang.term :as t]))

(defn- host? [t q] (and (= :host (:op t)) (= q (:name t))))

(defn stages
  "The fold of a fusable body: {:f :init :stages [[:map g] [:filter p] ..]
   (innermost first) :source xs-term}, or nil."
  [body]
  (when (and (= :app (:op body)) (host? (:fn body) 'clojure.core/reduce) (= 3 (count (:args body))))
    (let [[f init chain] (:args body)]
      (loop [c chain acc []]
        (cond
          (= :local (:op c)) {:f f :init init :stages acc :source c}
          (and (= :app (:op c)) (= 2 (count (:args c)))
               (or (host? (:fn c) 'clojure.core/map) (host? (:fn c) 'clojure.core/filter)))
          (recur (second (:args c)) (cons [(if (host? (:fn c) 'clojure.core/map) :map :filter) (first (:args c))] acc))
          :else nil)))))

(defn- step
  "The loop step for element term `x` through `stages` (innermost first)."
  [f acc stages x]
  (if-let [[[kind s] & more] (seq stages)]
    (case kind
      :map (let [y (t/fresh "y")] (t/let1 y (t/app s [x]) (step f acc more (t/local y))))
      :filter (t/if* (t/app s [x]) (step f acc more x) (t/local acc)))
    (t/app f [(t/local acc) x])))

(defn fuse
  "The fused candidate for `fn-term`, or nil when it is not a fold of
   map and filter stages over its single parameter."
  [fn-term]
  (let [[{:keys [params rest body]} & more] (:arities fn-term)]
    (when (and (= :fn (:op fn-term)) (nil? more) (nil? rest) (= 1 (count params)))
      (when-let [{:keys [f init stages source]} (stages body)]
        (when (= (first params) (:name source))
          (let [xs (t/fresh "xs")
                i (t/fresh "i") acc (t/fresh "acc") i0 (t/fresh "i") acc0 (t/fresh "acc")
                r (t/fresh "r") e (t/fresh "e") self (t/fresh "fuse") x (t/fresh "x")
                xs-t (t/local xs)
                loop-body (t/if* (t/app (t/host 'clojure.core/<) [(t/local i) (t/app (t/host 'clojure.core/count) [xs-t])])
                                 (t/let1 x (t/app (t/host 'clojure.core/nth) [xs-t (t/local i)])
                                 (t/let1 r (step f acc stages (t/local x))
                                         (t/if* (t/app (t/host 'clojure.core/reduced?) [(t/local r)])
                                                (t/app (t/host 'clojure.core/deref) [(t/local r)])
                                                {:op :recur :target self :arity 0
                                                 :args [(t/app (t/host 'clojure.core/inc) [(t/local i)]) (t/local r)]})))
                                 (t/local acc))
                the-loop (t/let1 i0 (t/const 0)
                                 (t/let1 acc0 init
                                         (t/app (t/fn-term self [(t/arity [i acc] nil loop-body)])
                                                [(t/local i0) (t/local acc0)])))
                reference (t/substitute body {(first params) xs-t})]
            (t/fn-term nil [(t/arity [xs] nil {:op :try :body the-loop
                                               :catches [{:class Throwable :name e :body reference}]
                                               :finally nil})])))))))

(defn- ordered-binders [t]
  (case (:op t)
    :fn (cond-> (vec (when (:self t) [(:self t)]))
          true (into (mapcat (fn [a] (cond-> (:params a) (:rest a) (conj (:rest a)))) (:arities t))))
    :let [(:name t)]
    :letrec (mapv first (:bindings t))
    :try (mapv :name (:catches t))
    []))

(defn- local-names
  "The locals bound in `t`, in pre-order."
  [t]
  (distinct (mapcat ordered-binders (t/nodes t))))

(defn alpha=
  "Are terms `a` and `b` equal up to the names of their locals?"
  [a b]
  (let [canon (fn [t] (t/->form (t/rename t (zipmap (local-names t) (map #(symbol (str "v" %)) (range))))))]
    (= (canon a) (canon b))))
