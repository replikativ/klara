(ns klara.compile.pe
  "K1 -> K1. Adapted from Christian Weilbach's Apache-2.0 raster scalar
  partial evaluator: propagation, trivial let inlining, dead branches,
  constant folding and fuel-bounded fixpoint. Obligation: never move or
  duplicate effects or failing computations. Numeric identities without
  type evidence are deliberately refused (overflow, NaN, signed zero)."
  (:require [klara.compile.ir :as ir] [klara.core :as c]))

(def foldable '#{+ - * / quot rem mod inc dec < > <= >= = not= not zero? pos? neg? even? odd? identity vector hash-map list first second nth get count})
(defn literal-data? [x]
  (or (nil? x) (boolean? x) (number? x) (string? x) (keyword? x) (symbol? x) (char? x)
      (and (or (vector? x) (list? x) (map? x) (set? x))
           (every? literal-data? (if (map? x) (mapcat identity x) x)))))

(defn step [t]
  (let [t (ir/map-children step t)]
    (case (:op t)
      :let (if (ir/trivial? (:init t))
             (ir/substitute (:body t) {(:name t) (:init t)}) t)
      :if (if (= :quote (get-in t [:test :op]))
            (if (get-in t [:test :datum]) (:then t) (:else t)) t)
      :prim (cond
              (and (= 'identity (:name t)) (= 1 (count (:args t)))) (first (:args t))
              (and (foldable (:name t)) (every? #(and (= :quote (:op %)) (literal-data? (:datum %))) (:args t)))
              (try (c/quote* (apply (c/prims (:name t)) (map :datum (:args t))))
                   (catch Throwable _ t))
              :else t)
      :app (let [f (:fn t)]
             (if (and (= :fn (:op f)) (not (:rest? f)) (= (:arity f) (count (:args t))))
               (reduce (fn [b [p a]] {:op :let :name p :init a :body b})
                       (:body f) (reverse (map vector (:params f) (:args t)))) t))
      t)))

(defn run [t fuel]
  (loop [t t n 0]
    (if (>= n fuel) {:term t :rounds n :fuel-exhausted? true}
        (let [u (step t)]
          (if (= t u) {:term t :rounds n :fuel-exhausted? false}
              (recur u (inc n)))))))
