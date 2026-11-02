(ns showcases.speculate-fail-continue
  "Speculate, fail, keep going.

  `settle` sums a ledger. Refunds (negative amounts) are rare and need a
  review, which is an effect: someone outside the loop decides. The loop
  compiles as it is, its perform leaving to the interpreter (L4.exec.leave),
  and that candidate calls `fee` like any other. The profile of a day of
  normal traffic shows the refund branch was never taken, so the default
  specializer goes further: it compiles the loop speculating that the branch
  stays cold, and inlines `fee` on the hot path. When the
  refund comes, three quarters into a large ledger, compiled code leaves to
  the interpreter at exactly that iteration; the interpreter performs the
  review, with the handler's continuation, and finishes the loop. Nothing
  runs twice. Then the helper changes: the speculating loop inlined it, so
  it no longer applies, and the plain candidate, which calls the helper,
  runs instead; a world from before the change keeps the speculating loop."
  (:require [klara.effect :refer [perform handle]]
            [klara.jit :as jit]
            [klara.compiler :as compiler]
            [klara.world :as world]
            [klara.profile :as profile]))

(defn fee [amount] (quot amount 100))

(defn settle [txs]
  (loop [i 0 balance 0]
    (if (< i (count txs))
      (let [amount (nth txs i)]
        (if (neg? amount)
          (recur (inc i) (+ balance (perform :review amount)))   ; rare: needs a decision
          (recur (inc i) (+ balance (- amount (fee amount))))))
      balance)))

(def ledger (vec (for [i (range 400000)] (if (= i 300000) -500 (+ 100 (mod (* i 7919) 900))))))

(def reviews (atom 0))
(defn reviewed
  "Run f, reviewing refunds by accepting them; counts the reviews."
  [f]
  (reset! reviews 0)
  (handle {:review (fn [k amount] (swap! reviews inc) (k amount))} (f)))

(defn ms [f] (let [t (System/nanoTime) r (f)] [(/ (- (System/nanoTime) t) 1000000.0) r]))

;; A day of normal traffic: the refund branch is never taken.
(settle (subvec ledger 0 2000))
(def interpreted                             ; measuring is not training
  (profile/without (fn [] (dotimes [_ 3] (reviewed (fn [] (settle ledger))))
                          (ms #(reviewed (fn [] (settle ledger)))))))

(def plain (compiler/optimize! 'showcases.speculate-fail-continue/settle))   ; without speculation
(def plain-premises (mapv first (:premises plain)))
(def outcome (jit/compile! 'showcases.speculate-fail-continue/settle))       ; the default specializer
(dotimes [_ 3] (reviewed (fn [] (settle ledger))))
(def compiled (ms #(reviewed (fn [] (settle ledger)))))
(def path (:last-path (compiler/explain settle)))
(def reentries (:reentries (compiler/explain settle)))
(def compiled-reviews @reviews)

;; The fee changes. The compiled loop assumed the old fee.
(def before (world/current))
(defn fee [amount] (quot amount 50))
(world/advance)
(def after-change (reviewed (fn [] (settle ledger))))
(def after-change-path (:last-path (compiler/explain settle)))   ; the speculating loop retired: it inlined the old fee
(def after-change-premises (vec (sort (map first (:premises (compiler/explain settle))))))
(def expected-after-change (reduce + (map (fn [a] (if (neg? a) a (- a (fee a)))) ledger)))
(def in-old-world (reviewed (fn [] (world/in before (fn [] (settle ledger))))))
(def old-world-path (world/in before (fn [] (:last-path (compiler/explain settle)))))

(def report
  {:without-speculation (:status plain)
   :without-speculation-premises plain-premises
   :premises (mapv first (:premises outcome))
   :status (:status outcome) :why (:message outcome)
   :speculations (:speculations outcome)
   :same-result (= (second interpreted) (second compiled))
   :reviews compiled-reviews
   :left-at-refund path
   :reentered-compiled-loop reentries
   :interpreted-ms (first interpreted)
   :compiled-ms (first compiled)
   :speedup (Math/round (/ (first interpreted) (first compiled)))
   :after-fee-change (- (second compiled) after-change)
   :after-fee-change-runs after-change-path
   :after-fee-change-premises after-change-premises
   :after-fee-change-correct (= after-change expected-after-change)
   :old-world-keeps (= in-old-world (second compiled))
   :old-world-path old-world-path})

(doseq [k [:without-speculation :status :why :speculations :same-result :reviews :left-at-refund :reentered-compiled-loop
           :interpreted-ms :compiled-ms :speedup :after-fee-change :after-fee-change-runs :old-world-keeps :old-world-path]]
  (println (str (name k) ":") (get report k)))

report
