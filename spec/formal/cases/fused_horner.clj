(ns fused-horner
  "Compiler composition (design/PLAN.md, showcase 3): two rewrites that know
  nothing of each other, admitted on different evidence, composed through
  the world.

  `score` folds a polynomial over the odd elements of a vector. Its fold of
  a map and a filter is fused into one loop by a law-licensed rewrite
  (L4.check.law: Law.foldl-map and Law.foldl-filter, proved once by the
  ansatz kernel; premises: the stages are pure; guard: the argument is a
  vector). `poly` is replaced by Horner's rule on a proof certificate under
  the range guard |x| <= 2^20 (L4.check.certificate,
  cases/certified_horner.clj). The fused loop calls `poly`, so it runs the
  certified code where its guard holds and the reference elsewhere; an
  error anywhere makes the loop give way to the reference fold, so the
  error observed is the reference's. Changing a stage retires the fused
  code; a world from before the change keeps it."
  (:require [klara.compiler :as compiler]
            [klara.world :as world]
            [certified-horner :as ch]))

(defn poly [x] (+ (+ (* 3 (* x x)) (* 5 x)) 7))
(defn keep? [x] (odd? x))
(defn score [xs] (reduce + 0 (map poly (filter keep? xs))))

;; the same fold, never compiled: the meaning the compiled code must match
(defn score-ref [xs] (reduce + 0 (map (fn [x] (+ (+ (* 3 (* x x)) (* 5 x)) 7)) (filter (fn [x] (odd? x)) xs))))

(def xs (vec (range 1 2001)))
(def big [1 3 3037000501])                 ; poly's x*x overflows at the last element

(def poly-outcome
  (compiler/optimize! 'fused-horner/poly
                      {:recipe (fn [_] (ch/horner 3 5 7))
                       :certificate {:kind :ansatz :range [(- ch/bound) ch/bound]
                                     :proof (ch/horner-proof 3 5 7 (- ch/bound) ch/bound)}}))
(def unlicensed (compiler/prepare (compiler/reference 'fused-horner/score) {:recipe klara.jit/fuse :name 'fused-horner/score}))
(def score-outcome (compiler/optimize! 'fused-horner/score {:recipe klara.jit/fuse :certificate {:kind :law}}))

(defn outcome-of [f] (try [:value (f)] (catch ArithmeticException e [:error :overflow])))

(def result (score xs))
(def score-path (:last-path (compiler/explain score)))
(def poly-path (:last-path (compiler/explain poly)))
(def on-big (outcome-of #(score big)))
(def on-list (score (seq xs)))              ; not a vector: the guard fails, the reference runs
(def list-path (:last-path (compiler/explain score)))

;; a stage changes: the fused code relied on keep? as it was
(def before (world/current))
(defn keep? [x] (even? x))
(world/advance)
(def after-change (score xs))
(def after-change-kind (:kind (compiler/explain score)))
(def in-old-world (world/in before (fn [] (score xs))))

{:poly (:status poly-outcome) :poly-evidence (get-in poly-outcome [:evidence :kernel])
 :without-law (:status unlicensed) :without-law-rule (:rule unlicensed)
 :score (:status score-outcome) :score-evidence (get-in score-outcome [:evidence :kind])
 :score-premises (mapv first (:premises score-outcome))
 :same (= result (score-ref xs)) :score-path score-path :poly-path poly-path
 :on-big (= on-big (outcome-of #(score-ref big))) :on-big-outcome on-big
 :on-list (= on-list result) :list-path list-path
 :after-change (= after-change (reduce + 0 (map poly (filter even? xs)))) :after-change-kind after-change-kind
 :old-world-keeps (= in-old-world result)}
