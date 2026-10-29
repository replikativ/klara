(ns consolidation.scalar-driver
  "An indexed finite driver over the actual encoded scalar callback.
   Core loop recognition/T0 machine adequacy are separate implementation bridges."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm] [consolidation.scalar-core :as scalar]
            [klara.fusion.kernel :as k]))

(def theorem-names ["scalar-run-shift" "scalar-indexed-prefix-fold"
                    "scalar-run-checked-sound" "scalar-checked-prefix-fold"])
(defn prove! []
  (binding [*ns* (the-ns 'consolidation.scalar-driver)]
    (reset! a/ansatz-env @scalar/proof-state)
    (clojure.core/refer 'consolidation.scalar-core :only '[scalarMeaning scalarPush scalarChecked scalarBind])
    (a/defn scalarZero [i :- Nat] Nat 0)
    (a/defn scalarAt [xs :- (List Nat)] (=> Nat Nat)
      (match xs
        [nil scalarZero]
        [(cons head tail) (fn [i :- Nat] (match i [zero head] [(succ previous) (scalarAt tail previous)]))]))
    (a/defn scalarTake [xs :- (List Nat)] (=> Nat (List Nat))
      (match xs
        [nil (fn [n :- Nat] (List.nil Nat))]
        [(cons head tail) (fn [n :- Nat]
                           (match n [zero (List.nil Nat)]
                                    [(succ previous) (List.cons Nat head (scalarTake tail previous))]))]))
    (a/defn scalarStep [p :- ScalarCore, acc :- Nat, x :- Nat] Nat
      (scalarMeaning p (scalarPush x (scalarPush acc scalarZero))))
    (a/defn scalarRun [count :- Nat] (=> ScalarCore (=> (List Nat) (=> Nat (=> Nat Nat))))
      (match count
        [zero (fn [p :- ScalarCore, xs :- (List Nat), index :- Nat, acc :- Nat] acc)]
        [(succ remaining)
         (fn [p :- ScalarCore, xs :- (List Nat), index :- Nat, acc :- Nat]
           (scalarRun remaining p xs (Nat.succ index) (scalarStep p acc (scalarAt xs index))))]))
    (a/theorem scalar-run-shift [count :- Nat, p :- ScalarCore, head :- Nat, tail :- (List Nat)]
      (forall [index :- Nat, acc :- Nat]
        (= Nat (scalarRun count p (List.cons Nat head tail) (Nat.succ index) acc)
               (scalarRun count p tail index acc)))
      (induction count)
      (all_goals (intro index) (intro acc))
      (all_goals (simp only [scalarRun.eq_1 scalarRun.eq_2 scalarAt.eq_2]))
      (all_goals (try (rfl)))
      (exact (ih_n (Nat.succ index) (scalarStep p acc (scalarAt tail index)))))
    (a/theorem scalar-indexed-prefix-fold [xs :- (List Nat), p :- ScalarCore]
      (forall [count :- Nat, acc :- Nat, within :- (<= count (List.length xs))]
        (= Nat (scalarRun count p xs 0 acc)
               (List.foldl (scalarStep p) acc (scalarTake xs count))))
      (induction xs)
      (all_goals (intro count) (intro acc) (intro within))
      (all_goals (cases count))
      (all_goals (simp only [scalarRun.eq_1 scalarRun.eq_2 scalarTake.eq_1 scalarTake.eq_2 scalarAt.eq_2]))
      (all_goals (try (rfl)))
      (all_goals (try (omega)))
      (rw [(scalar-run-shift n p head tail 0 (scalarStep p acc head))])
      (exact (ih_tail n (scalarStep p acc head) (Nat.le_of_succ_le_succ within))))
    (a/defn scalarRunChecked [count :- Nat] (=> ScalarCore (=> (List Nat) (=> Nat (=> Nat (=> Nat (Option Nat))))))
      (match count
        [zero (fn [p :- ScalarCore, xs :- (List Nat), index :- Nat, acc :- Nat, cap :- Nat]
                (Option.some Nat acc))]
        [(succ remaining)
         (fn [p :- ScalarCore, xs :- (List Nat), index :- Nat, acc :- Nat, cap :- Nat]
           (scalarBind (scalarChecked p (scalarPush (scalarAt xs index) (scalarPush acc scalarZero)) cap)
             (fn [next :- Nat] (scalarRunChecked remaining p xs (Nat.succ index) next cap))))]))
    (a/inductive ScalarRunSafe [cap Nat, p ScalarCore, xs (List Nat)] :in Prop :indices [count Nat, index Nat, acc Nat]
      (done [index Nat] [acc Nat] :where [0 index acc])
      (step [remaining Nat] [index Nat] [acc Nat] [upper Nat]
            [hb (ScalarBound cap (scalarPush (scalarAt xs index) (scalarPush acc scalarZero)) p upper)]
            [rest (ScalarRunSafe cap p xs remaining (Nat.succ index) (scalarStep p acc (scalarAt xs index)))]
            :where [(Nat.succ remaining) index acc]))
    (a/theorem scalar-run-checked-sound
      [cap :- Nat, p :- ScalarCore, xs :- (List Nat), count :- Nat, index :- Nat, acc :- Nat,
       hs :- (ScalarRunSafe cap p xs count index acc)]
      (= (Option Nat) (scalarRunChecked count p xs index acc cap)
         (Option.some Nat (scalarRun count p xs index acc)))
      (induction hs)
      (all_goals (simp only [scalarRunChecked.eq_1 scalarRunChecked.eq_2 scalarRun.eq_1 scalarRun.eq_2]))
      (all_goals (try (rfl)))
      (rw [(scalar-checked-sound
              (scalarPush (scalarAt xs index) (scalarPush acc scalarZero)) cap p upper hb
              (scalarPush (scalarAt xs index) (scalarPush acc scalarZero))
              (fn [i :- Nat] (Nat.le_refl (scalarPush (scalarAt xs index) (scalarPush acc scalarZero) i))))])
      (simp only [scalarBind.eq_2])
      (exact ih_rest))
    (a/theorem scalar-checked-prefix-fold
      [xs :- (List Nat), p :- ScalarCore, count :- Nat, acc :- Nat, cap :- Nat,
       within :- (<= count (List.length xs)), hs :- (ScalarRunSafe cap p xs count 0 acc)]
      (= (Option Nat) (scalarRunChecked count p xs 0 acc cap)
         (Option.some Nat (List.foldl (scalarStep p) acc (scalarTake xs count))))
      (rw [(scalar-run-checked-sound cap p xs count 0 acc hs)])
      (rw [(scalar-indexed-prefix-fold xs p count acc within)]))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "finite driver theorem failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))
