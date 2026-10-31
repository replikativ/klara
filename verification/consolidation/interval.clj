(ns consolidation.interval
  "Proof-producing bounds for nonnegative +/* expressions. The kernel model
   uses bounded Nat arithmetic; correspondence to checked JVM Long is separate."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k]))

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.interval)]
    (a/load-init!)
    (a/inductive BoundExpr []
      (lit [n Nat]) (arg) (add [left BoundExpr] [right BoundExpr])
      (mul [left BoundExpr] [right BoundExpr]))
    (a/defn boundValue [p :- BoundExpr] (=> Nat Nat)
      (match p
        [(lit n) (fn [x :- Nat] n)] [arg (fn [x :- Nat] x)]
        [(add left right) (fn [x :- Nat] (+ (boundValue left x) (boundValue right x)))]
        [(mul left right) (fn [x :- Nat] (* (boundValue left x) (boundValue right x)))]))
    (a/inductive BoundSafe [bound Nat, cap Nat] :in Prop :indices [p BoundExpr]
      (lit [n Nat] [h (Nat.le n cap)] :where [(BoundExpr.lit n)])
      (arg [h (Nat.le bound cap)] :where [BoundExpr.arg])
      (add [left BoundExpr] [right BoundExpr]
           [hl (BoundSafe bound cap left)] [hr (BoundSafe bound cap right)]
           [h (Nat.le (Nat.add (boundValue left bound) (boundValue right bound)) cap)]
           :where [(BoundExpr.add left right)])
      (mul [left BoundExpr] [right BoundExpr]
           [hl (BoundSafe bound cap left)] [hr (BoundSafe bound cap right)]
           [h (Nat.le (Nat.mul (boundValue left bound) (boundValue right bound)) cap)]
           :where [(BoundExpr.mul left right)]))
    (a/defn boundFits [p :- BoundExpr] (=> Nat (=> Nat Bool))
      (match p
        [(lit n) (fn [x :- Nat, cap :- Nat] (Nat.ble n cap))]
        [arg (fn [x :- Nat, cap :- Nat] (Nat.ble x cap))]
        [(add left right)
         (fn [x :- Nat, cap :- Nat]
           (Bool.and (boundFits left x cap)
                     (Bool.and (boundFits right x cap)
                               (Nat.ble (+ (boundValue left x) (boundValue right x)) cap))))]
        [(mul left right)
         (fn [x :- Nat, cap :- Nat]
           (Bool.and (boundFits left x cap)
                     (Bool.and (boundFits right x cap)
                               (Nat.ble (* (boundValue left x) (boundValue right x)) cap))))]))
    (a/defn boundChecked [p :- BoundExpr, x :- Nat, cap :- Nat] (Option Nat)
      (match (boundFits p x cap)
        [true (Option.some Nat (boundValue p x))] [false (Option.none Nat)]))
    (a/theorem bound-monotone [p :- BoundExpr]
      (forall [x :- Nat, bound :- Nat] (=> (<= x bound) (<= (boundValue p x) (boundValue p bound))))
      (induction p)
      (all_goals (intro x) (intro bound) (intro hx))
      (all_goals (simp only [boundValue.eq_1 boundValue.eq_2 boundValue.eq_3 boundValue.eq_4]))
      (exact (Nat.le_refl n))
      (exact hx)
      (exact (Nat.add_le_add (ih_left x bound hx) (ih_right x bound hx)))
      (exact (Nat.le_trans (Nat.mul_le_mul_right (boundValue right x) (ih_left x bound hx))
                           (Nat.mul_le_mul_left (boundValue left bound) (ih_right x bound hx)))))
    (a/theorem bound-value-safe [bound :- Nat, cap :- Nat, p :- BoundExpr,
                                h :- (BoundSafe bound cap p)]
      (<= (boundValue p bound) cap)
      (cases h)
      (all_goals (simp only [boundValue.eq_1 boundValue.eq_2 boundValue.eq_3 boundValue.eq_4]))
      (all_goals (assumption)))
    (a/theorem bound-and-true [a :- Bool, b :- Bool,
                                ha :- (= Bool a true), hb :- (= Bool b true)]
      (= Bool (Bool.and a b) true)
      (rw [ha hb]))
    (a/theorem bound-fits-sound [bound :- Nat, cap :- Nat, p :- BoundExpr,
                                   h :- (BoundSafe bound cap p)]
      (forall [x :- Nat] (=> (<= x bound)
                            (= Bool (boundFits p x cap) true)))
      (induction h)
      (all_goals (intro x) (intro hx))
      (all_goals (simp only [boundFits.eq_1 boundFits.eq_2 boundFits.eq_3 boundFits.eq_4
                            boundValue.eq_1 boundValue.eq_2 boundValue.eq_3 boundValue.eq_4]))
      (all_goals (try (exact (Nat.ble_eq_true_of_le h))))
      (all_goals (try (exact (Nat.ble_eq_true_of_le (Nat.le_trans hx h)))))
      (all_goals (try
        (exact (bound-and-true _ _ (ih_hl x hx)
          (bound-and-true _ _ (ih_hr x hx)
            (Nat.ble_eq_true_of_le
              (Nat.le_trans (Nat.add_le_add (bound-monotone left x bound hx)
                                           (bound-monotone right x bound hx)) h)))))))
      (all_goals (try
        (exact (bound-and-true _ _ (ih_hl x hx)
          (bound-and-true _ _ (ih_hr x hx)
            (Nat.ble_eq_true_of_le
              (Nat.le_trans
                (Nat.le_trans (Nat.mul_le_mul_right (boundValue right x) (bound-monotone left x bound hx))
                              (Nat.mul_le_mul_left (boundValue left bound) (bound-monotone right x bound hx))) h))))))))
    (a/theorem bound-checked-sound
      [bound :- Nat, cap :- Nat, p :- BoundExpr, h :- (BoundSafe bound cap p), x :- Nat, hx :- (<= x bound)]
      (= (Option Nat) (boundChecked p x cap) (Option.some Nat (boundValue p x)))
      (simp only [boundChecked])
      (rw [(bound-fits-sound bound cap p h x hx)]))
    (let [en (a/env)]
      (doseq [name ["bound-monotone" "bound-value-safe" "bound-fits-sound" "bound-checked-sound"]
              :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "independent bounds proof check failed" {:theorem name}))))
      en)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn- le-proof [n cap]
  ;; The comparison reduces in the kernel; no host Boolean is an axiom.
  (let [n (e/lit-nat (biginteger n)) cap (e/lit-nat (biginteger cap))
        equality (e/app* (k/c "Eq.refl" [k/l1]) k/Bool (k/c "Bool.true"))]
    (e/app* (k/c "Nat.le_of_ble_eq_true") n cap equality)))

(defn certify
  "Re-elaborate actual scalar core and produce a proof for every intermediate.
   N-ary arithmetic is left-folded, including the operation's unit."
  [core max-x cap]
  (when-not (and (instance? Long max-x) (<= 0 max-x)
                 (instance? Long cap) (<= 0 cap))
    (throw (ex-info "bounds require nonnegative Longs" {:reason :domain})))
  (let [en @proof-state bound (e/lit-nat (biginteger max-x)) capacity (e/lit-nat (biginteger cap))]
    (letfn [(node [op args n]
              (when (> n cap) (throw (ex-info "intermediate exceeds capacity" {:reason :overflow :bound n})))
              (let [term (apply e/app* (k/c (str "BoundExpr." (name op))) (map :term args))
                    proof (apply e/app* (k/c (str "BoundSafe." (name op)))
                                 (concat [bound capacity] (map :term args) (map :proof args) [(le-proof n cap)]))]
                {:term term :proof proof :upper n}))
            (literal [n]
              (when-not (and (instance? Long n) (<= 0 n cap))
                (throw (ex-info "invalid bounded literal" {:reason :overflow})))
              {:term (e/app (k/c "BoundExpr.lit") (e/lit-nat (biginteger n)))
               :proof (e/app* (k/c "BoundSafe.lit") bound capacity (e/lit-nat (biginteger n)) (le-proof n cap))
               :upper (bigint n)})
            (go [t]
              (case (:op t)
                :quote (literal (:datum t))
                :local (if (zero? (:index t))
                         (do (when (> max-x cap) (throw (ex-info "argument exceeds capacity" {:reason :overflow})))
                             {:term (k/c "BoundExpr.arg")
                              :proof (e/app* (k/c "BoundSafe.arg") bound capacity (le-proof max-x cap))
                              :upper (bigint max-x)})
                         (throw (ex-info "only the polynomial argument is in scope" {:reason :scope})))
                :prim (let [[op f unit] (case (:name t)
                                         + [:add +' 0] * [:mul *' 1]
                                         (throw (ex-info "unsupported bound operation" {:reason :operation})))]
                        (reduce (fn [left arg]
                                  (let [right (go arg)]
                                    (node op [left right] (f (:upper left) (:upper right)))))
                                (literal unit) (:args t)))
                (throw (ex-info "unsupported bounded expression" {:reason :operation})) ))]
      (let [result (go core) goal (e/app* (k/c "BoundSafe") bound capacity (:term result))]
        (when-not (env/verifies? en goal (:proof result))
          (throw (ex-info "bounds proof rejected" {:reason :proof})))
        (assoc result :goal goal :environment en
               :checked-arithmetic-proof
               (e/app* (k/c "bound-checked-sound") bound capacity (:term result) (:proof result)))))))
