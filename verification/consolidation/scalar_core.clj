(ns consolidation.scalar-core
  "Restricted original-Core scalar semantics. Proofs cover this encoded fragment;
   runtime-map decoding and T0/JVM correspondence remain explicit boundaries."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as nm]
            [consolidation.interval :as interval] [klara.core :as c]
            [klara.fusion.kernel :as k]))

(def theorem-names
  ["scalar-env-push" "scalar-bound-value" "scalar-checked-sound"])

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.scalar-core)]
    (reset! a/ansatz-env @interval/proof-state)
    ;; Binary primitive applications only. N-ary applications must not be
    ;; silently reassociated into these constructors by the decoder.
    (a/inductive ScalarCore []
      (lit [value Nat]) (local [index Nat])
      (add [left ScalarCore] [right ScalarCore])
      (mul [left ScalarCore] [right ScalarCore])
      (let_ [init ScalarCore] [body ScalarCore]))
    (a/defn scalarPush [value :- Nat, rho :- (=> Nat Nat), index :- Nat] Nat
      (match index [zero value] [(succ previous) (rho previous)]))
    (a/defn scalarMeaning [p :- ScalarCore] (=> (=> Nat Nat) Nat)
      (match p
        [(lit value) (fn [rho :- (=> Nat Nat)] value)]
        [(local index) (fn [rho :- (=> Nat Nat)] (rho index))]
        [(add left right) (fn [rho :- (=> Nat Nat)] (+ (scalarMeaning left rho) (scalarMeaning right rho)))]
        [(mul left right) (fn [rho :- (=> Nat Nat)] (* (scalarMeaning left rho) (scalarMeaning right rho)))]
        [(let_ init body) (fn [rho :- (=> Nat Nat)] (scalarMeaning body (scalarPush (scalarMeaning init rho) rho)))]))
    (a/defn scalarBind [answer :- (Option Nat), f :- (=> Nat (Option Nat))] (Option Nat)
      (match answer [none (Option.none Nat)] [(some value) (f value)]))
    (a/defn scalarCheck [value :- Nat, cap :- Nat] (Option Nat)
      (match (Nat.ble value cap) [true (Option.some Nat value)] [false (Option.none Nat)]))
    (a/defn scalarChecked [p :- ScalarCore] (=> (=> Nat Nat) (=> Nat (Option Nat)))
      (match p
        [(lit value) (fn [rho :- (=> Nat Nat), cap :- Nat] (scalarCheck value cap))]
        [(local index) (fn [rho :- (=> Nat Nat), cap :- Nat] (scalarCheck (rho index) cap))]
        [(add left right)
         (fn [rho :- (=> Nat Nat), cap :- Nat]
           (scalarBind (scalarChecked left rho cap)
             (fn [a :- Nat] (scalarBind (scalarChecked right rho cap)
                             (fn [b :- Nat] (scalarCheck (+ a b) cap))))))]
        [(mul left right)
         (fn [rho :- (=> Nat Nat), cap :- Nat]
           (scalarBind (scalarChecked left rho cap)
             (fn [a :- Nat] (scalarBind (scalarChecked right rho cap)
                             (fn [b :- Nat] (scalarCheck (* a b) cap))))))]
        [(let_ init body)
         (fn [rho :- (=> Nat Nat), cap :- Nat]
           (scalarBind (scalarChecked init rho cap)
             (fn [value :- Nat] (scalarChecked body (scalarPush value rho) cap))))]))
    (a/inductive ScalarBound [cap Nat] :in Prop :indices [bounds (=> Nat Nat), p ScalarCore, upper Nat]
      (lit [bounds (=> Nat Nat)] [value Nat] [fits (Nat.le value cap)] :where [bounds (ScalarCore.lit value) value])
      (local [bounds (=> Nat Nat)] [index Nat] [fits (Nat.le (bounds index) cap)] :where [bounds (ScalarCore.local index) (bounds index)])
      (add [bounds (=> Nat Nat)] [left ScalarCore] [right ScalarCore] [lu Nat] [ru Nat]
           [hl (ScalarBound cap bounds left lu)] [hr (ScalarBound cap bounds right ru)]
           [fits (Nat.le (Nat.add lu ru) cap)] :where [bounds (ScalarCore.add left right) (Nat.add lu ru)])
      (mul [bounds (=> Nat Nat)] [left ScalarCore] [right ScalarCore] [lu Nat] [ru Nat]
           [hl (ScalarBound cap bounds left lu)] [hr (ScalarBound cap bounds right ru)]
           [fits (Nat.le (Nat.mul lu ru) cap)] :where [bounds (ScalarCore.mul left right) (Nat.mul lu ru)])
      (let_ [bounds (=> Nat Nat)] [init ScalarCore] [body ScalarCore] [iu Nat] [bu Nat]
            [hi (ScalarBound cap bounds init iu)]
            [hb (ScalarBound cap (scalarPush iu bounds) body bu)]
            :where [bounds (ScalarCore.let_ init body) bu]))
    (a/theorem scalar-env-push
      [rho :- (=> Nat Nat), bounds :- (=> Nat Nat), value :- Nat, upper :- Nat,
       henv :- (forall [i :- Nat] (<= (rho i) (bounds i))), hv :- (<= value upper)]
      (forall [i :- Nat] (<= (scalarPush value rho i) (scalarPush upper bounds i)))
      (intro i) (cases i)
      (all_goals (simp only [scalarPush.eq_1 scalarPush.eq_2]))
      (all_goals (try (exact hv))) (all_goals (exact (henv n))))
    (a/theorem scalar-bound-value
      [bounds :- (=> Nat Nat), cap :- Nat, p :- ScalarCore, upper :- Nat,
       h :- (ScalarBound cap bounds p upper)]
      (forall [rho :- (=> Nat Nat), henv :- (forall [i :- Nat] (<= (rho i) (bounds i)))]
        (<= (scalarMeaning p rho) upper))
      (induction h)
      (all_goals (intro rho) (intro henv))
      (all_goals (simp only [scalarMeaning.eq_1 scalarMeaning.eq_2 scalarMeaning.eq_3 scalarMeaning.eq_4 scalarMeaning.eq_5]))
      (exact (Nat.le_refl value))
      (exact (henv index))
      (exact (Nat.add_le_add (ih_hl rho henv) (ih_hr rho henv)))
      (exact (Nat.le_trans (Nat.mul_le_mul_right (scalarMeaning right rho) (ih_hl rho henv))
                           (Nat.mul_le_mul_left lu (ih_hr rho henv))))
      (exact (ih_hb (scalarPush (scalarMeaning init rho) rho)
                   (scalar-env-push rho bounds (scalarMeaning init rho) iu henv (ih_hi rho henv)))))
    (a/theorem scalar-checked-sound
      [bounds :- (=> Nat Nat), cap :- Nat, p :- ScalarCore, upper :- Nat,
       h :- (ScalarBound cap bounds p upper)]
      (forall [rho :- (=> Nat Nat), henv :- (forall [i :- Nat] (<= (rho i) (bounds i)))]
        (= (Option Nat) (scalarChecked p rho cap) (Option.some Nat (scalarMeaning p rho))))
      (induction h)
      (all_goals (intro rho) (intro henv))
      (all_goals (simp only [scalarChecked.eq_1 scalarChecked.eq_2 scalarChecked.eq_3 scalarChecked.eq_4 scalarChecked.eq_5
                             scalarMeaning.eq_1 scalarMeaning.eq_2 scalarMeaning.eq_3 scalarMeaning.eq_4 scalarMeaning.eq_5]))
      (all_goals (try (rw [(ih_hl rho henv)])))
      (all_goals (simp only [scalarBind.eq_2]))
      (all_goals (try (rw [(ih_hr rho henv)])))
      (all_goals (simp only [scalarBind.eq_2 scalarCheck]))
      (all_goals (try (rw [(Nat.ble_eq_true_of_le fits)])))
      (all_goals (try (rw [(Nat.ble_eq_true_of_le (Nat.le_trans (henv index) fits))])))
      (all_goals (try (rfl)))
      (all_goals (try (rw [(Nat.ble_eq_true_of_le
                              (Nat.le_trans (Nat.add_le_add (scalar-bound-value bounds cap left lu hl rho henv)
                                                           (scalar-bound-value bounds cap right ru hr rho henv)) fits))])))
      (all_goals (try (rw [(Nat.ble_eq_true_of_le
                              (Nat.le_trans
                                (Nat.le_trans
                                  (Nat.mul_le_mul_right (scalarMeaning right rho) (scalar-bound-value bounds cap left lu hl rho henv))
                                  (Nat.mul_le_mul_left lu (scalar-bound-value bounds cap right ru hr rho henv))) fits))])))
      (all_goals (try (rfl)))
      (rw [(ih_hi rho henv)])
      (simp only [scalarBind.eq_2])
      (exact (ih_hb (scalarPush (scalarMeaning init rho) rho)
                   (scalar-env-push rho bounds (scalarMeaning init rho) iu henv
                     (scalar-bound-value bounds cap init iu hi rho henv)))))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "scalar correspondence theorem failed" {:theorem name})))) en)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn- decline! [reason message]
  (throw (ex-info message {:reason :scalar-core :check reason})))
(defn- nat [n] (e/lit-nat (biginteger n)))
(defn- constructor [name & args] (apply e/app* (k/c (str "ScalarCore." name)) args))
(defn bounds-expression [bounds]
  (let [i (k/fvar!) zero (k/lam* [[i "index" k/Nat]] (nat 0))]
    (reduce #(e/app* (k/c "scalarPush") (nat %2) %1) zero bounds)))

(defn encode-body
  "Small syntax-only boundary. No inlining, substitution or reassociation.
   A lambda around the body checks the exact de Bruijn binder interface."
  [body arity]
  (when-not (and (integer? arity) (<= 0 arity)) (decline! :arity "invalid scalar arity"))
  (c/assert-wf! (c/lam arity body))
  (letfn [(go [t]
            (case (:op t)
              :quote (let [v (:datum t)]
                       (when-not (and (instance? Long v) (<= 0 v))
                         (decline! :literal "only nonnegative Long literals are admitted"))
                       (constructor "lit" (nat v)))
              :local (constructor "local" (nat (:index t)))
              :let (constructor "let_" (go (:init t)) (go (:body t)))
              :prim (do (when-not (and (#{'+ '*} (:name t)) (= 2 (count (:args t))))
                          (decline! :primitive "only exact binary +/* applications are admitted"))
                        (apply constructor (if (= '+ (:name t)) "add" "mul") (map go (:args t))))
              (decline! :syntax "effect/control outside the restricted scalar fragment")))]
    (go body)))

(defn- le-proof [value cap]
  (e/app* (k/c "Nat.le_of_ble_eq_true") (nat value) (nat cap)
          (e/app* (k/c "Eq.refl" [k/l1]) k/Bool (k/c "Bool.true"))))

(defn- bound-goal [bounds cap core upper]
  (e/app* (k/c "ScalarBound") (nat cap) bounds core (nat upper)))
(defn- scalar-goals [bounds cap core upper]
  (let [[rho index henv] (repeatedly 3 k/fvar!)
        rho-type (k/arrow k/Nat k/Nat)
        math (e/app* (k/c "scalarMeaning") core (e/fvar rho))
        below (fn [a b] (e/app* (k/c "Nat.le") a b))
        assumption (k/pi* [[index "index" k/Nat]]
                          (below (e/app (e/fvar rho) (e/fvar index)) (e/app bounds (e/fvar index))))
        quantify #(k/pi* [[rho "rho" rho-type] [henv "bounded" assumption]] %)]
    {:checked (quantify (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                              (e/app* (k/c "scalarChecked") core (e/fvar rho) (nat cap))
                              (e/app* (k/c "Option.some" [k/l0]) k/Nat math)))
     :value (quantify (below math (nat upper)))}))

(defn certify-body
  "A universal proof for an exact original body and ordered argument bounds.
   The certified semantics uses total functional environments. encode-body
   enforces actual finite scope; T0/Long/backend correspondence is still tested."
  ([body input-bounds] (certify-body body input-bounds Long/MAX_VALUE))
  ([body input-bounds cap]
   (when-not (and (vector? input-bounds) (instance? Long cap) (<= 0 cap)
                  (every? #(and (instance? Long %) (<= 0 % cap)) input-bounds))
     (decline! :bounds "bounds and capacity must be nonnegative Longs"))
   (let [en @proof-state encoded (encode-body body (count input-bounds))
         initial-bounds (bounds-expression input-bounds)
         capacity (nat cap)]
     (letfn [(node [t local-bounds bounds]
               (let [make (fn [kind core upper arguments]
                            (when (> upper cap) (decline! :overflow "scalar intermediate exceeds capacity"))
                            {:core core :upper upper
                             :proof (apply e/app* (k/c (str "ScalarBound." kind)) capacity bounds arguments)})]
                 (case (:op t)
                   :quote (let [v (:datum t)]
                            (make "lit" (constructor "lit" (nat v)) v [(nat v) (le-proof v cap)]))
                   :local (let [i (:index t) upper (nth local-bounds (- (count local-bounds) 1 i))]
                            (make "local" (constructor "local" (nat i)) upper [(nat i) (le-proof upper cap)]))
                   :let (let [init (node (:init t) local-bounds bounds)
                              pushed (e/app* (k/c "scalarPush") (nat (:upper init)) bounds)
                              body (node (:body t) (conj local-bounds (:upper init)) pushed)
                              core (constructor "let_" (:core init) (:core body))]
                          (make "let_" core (:upper body)
                                [(:core init) (:core body) (nat (:upper init)) (nat (:upper body))
                                 (:proof init) (:proof body)]))
                   :prim (let [[left right] (mapv #(node % local-bounds bounds) (:args t))
                               add? (= '+ (:name t)) kind (if add? "add" "mul")
                               upper ((if add? +' *') (:upper left) (:upper right))
                               core (constructor kind (:core left) (:core right))]
                           (make kind core upper
                                 [(:core left) (:core right) (nat (:upper left)) (nat (:upper right))
                                  (:proof left) (:proof right) (le-proof upper cap)])))))]
       (let [result (node body input-bounds initial-bounds)
             goal (bound-goal initial-bounds cap encoded (:upper result))
             goals (scalar-goals initial-bounds cap encoded (:upper result))
             proof-args [initial-bounds capacity encoded (nat (:upper result)) (:proof result)]
             checked-proof (apply e/app* (k/c "scalar-checked-sound") proof-args)
             value-proof (apply e/app* (k/c "scalar-bound-value") proof-args)]
         (when-not (and (= encoded (:core result))
                        (env/verifies? en goal (:proof result))
                        (env/verifies? en (:checked goals) checked-proof)
                        (env/verifies? en (:value goals) value-proof))
           (decline! :proof "actual scalar endpoint proof failed"))
         {:source body :source-id (c/code-id (c/lam (count input-bounds) body))
          :arity (count input-bounds) :input-bounds input-bounds :capacity cap
          :core encoded :upper (:upper result) :bound-goal goal :bound-proof (:proof result)
          :checked-goal (:checked goals) :checked-proof checked-proof
          :value-goal (:value goals) :value-proof value-proof
          :goal-sha256 (k/expr-hash (:checked goals)) :proof-sha256 (k/expr-hash checked-proof)
          :bridges [:runtime-map-decoder :finite-environment-embedding :T0-CEK :JVM-Long]})))))

(defn verify-body-witness? [body input-bounds witness]
  (try
    (let [en @proof-state core (encode-body body (count input-bounds))
          cap (:capacity witness) upper (:upper witness)
          bounds (bounds-expression input-bounds)
          goals (scalar-goals bounds cap core upper)]
      (and (vector? input-bounds) (instance? Long cap) (<= 0 cap)
           (every? #(and (instance? Long %) (<= 0 % cap)) input-bounds)
           (= input-bounds (:input-bounds witness)) (= (count input-bounds) (:arity witness))
           (= (c/code-id (c/lam (count input-bounds) (:source witness))) (:source-id witness))
           (= (c/code-id (c/lam (count input-bounds) body)) (:source-id witness))
           (= core (:core witness))
           (= (bound-goal bounds cap core upper) (:bound-goal witness))
           (= (:checked goals) (:checked-goal witness)) (= (:value goals) (:value-goal witness))
           (= (:goal-sha256 witness) (k/expr-hash (:checked goals)))
           (= (:proof-sha256 witness) (k/expr-hash (:checked-proof witness)))
           (env/verifies? en (:bound-goal witness) (:bound-proof witness))
           (env/verifies? en (:checked goals) (:checked-proof witness))
           (env/verifies? en (:value goals) (:value-proof witness))))
    (catch Exception _ false)))
