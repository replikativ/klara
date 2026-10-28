(ns klara.effect-class
  "Small, structural T0 admission check. Unknown clauses are general."
  (:require [klara.core :as c]))

(defn- mentions? [t index]
  (case (:op t)
    :local (= index (:index t))
    :quote false
    :fn (mentions? (:body t) (+ index (:arity t) (if (:rest? t) 1 0)))
    :let (or (mentions? (:init t) index) (mentions? (:body t) (inc index)))
    ;; Other binders are deliberately unknown, never a claim of absence.
    (:letrec :handle :code :esc) true
    (boolean (some #(mentions? % index) (c/children t)))))

(defn classify
  "Classify a fixed-arity core clause, whose last parameter is k.
  No declaration or host function is trusted. The tail fragment admits
  direct final k calls, conditionals and lets without any other k use."
  [t]
  (when (and (= :fn (:op t)) (pos? (:arity t)) (not (:rest? t)))
    (letfn [(tail? [b i]
              (or (not (mentions? b i))
                  (case (:op b)
                    :app (and (= {:op :local :index i} (:fn b))
                              (= 1 (count (:args b)))
                              (not-any? #(mentions? % i) (:args b)))
                    :let (and (not (mentions? (:init b) i)) (tail? (:body b) (inc i)))
                    :if (and (not (mentions? (:test b) i))
                             (tail? (:then b) i) (tail? (:else b) i))
                    false)))]
      (cond
        (not (mentions? (:body t) 0)) :abortive
        (tail? (:body t) 0) :tail
        :else :general))))
