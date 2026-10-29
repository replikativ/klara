(ns consolidation.scalar-finite
  "Finite de Bruijn environments for the admitted scalar syntax. Scope and
   lookup are kernel obligations; encoding JVM values remains a host boundary."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [consolidation.scalar-cek :as cek] [consolidation.scalar-core :as scalar]
            [ansatz.kernel.expr :as e] [klara.fusion.kernel :as k] [klara.core :as c]))
(def theorem-names ["scalar-finite-cons" "scalar-finite-lookup" "scalar-finite-push"
                    "scalar-bind-congr" "scalar-finite-checked" "scalar-finite-execution"])
(defn prove! []
  (binding [*ns* (the-ns 'consolidation.scalar-finite)]
    (reset! a/ansatz-env @cek/proof-state)
    (clojure.core/refer 'consolidation.scalar-core :only '[scalarCheck scalarBind scalarPush scalarChecked])
    (a/defn scalarFiniteEnv [xs :- (List Nat)] (=> Nat Nat)
      (match xs [nil (fn [i :- Nat] 0)]
                [(cons head tail) (fn [i :- Nat] (match i [zero head] [(succ previous) (scalarFiniteEnv tail previous)]))]))
    (a/defn scalarFiniteLookup [xs :- (List Nat)] (=> Nat (Option Nat))
      (match xs [nil (fn [i :- Nat] (Option.none Nat))]
                [(cons head tail) (fn [i :- Nat]
                                   (match i [zero (Option.some Nat head)] [(succ previous) (scalarFiniteLookup tail previous)]))]))
    (a/theorem scalar-finite-cons [xs :- (List Nat), value :- Nat, i :- Nat]
      (= Nat (scalarFiniteEnv (List.cons Nat value xs) i) (scalarPush value (scalarFiniteEnv xs) i))
      (cases i) (all_goals (rfl)))
    (a/theorem scalar-finite-lookup [xs :- (List Nat)]
      (forall [i :- Nat, within :- (<= (Nat.succ i) (List.length xs))]
        (= (Option Nat) (scalarFiniteLookup xs i) (Option.some Nat (scalarFiniteEnv xs i))))
      (induction xs)
      (all_goals (intro i) (intro within))
      (all_goals (cases i))
      (all_goals (simp only [scalarFiniteLookup scalarFiniteEnv List.length_nil List.length_cons] at *))
      (all_goals (try (rfl))) (all_goals (try (omega)))
      (all_goals (exact (ih_tail n (Nat.le_of_succ_le_succ within)))))
    (a/theorem scalar-finite-push [xs :- (List Nat), value :- Nat]
      (= (=> Nat Nat) (scalarFiniteEnv (List.cons Nat value xs)) (scalarPush value (scalarFiniteEnv xs)))
      (exact (funext (fn [i :- Nat] (scalar-finite-cons xs value i)))))
    (a/inductive ScalarScoped [] :in Prop :indices [depth Nat, p ScalarCore]
      (lit [depth Nat] [value Nat] :where [depth (ScalarCore.lit value)])
      (local [depth Nat] [index Nat] [within (Nat.le (Nat.succ index) depth)] :where [depth (ScalarCore.local index)])
      (add [depth Nat] [left ScalarCore] [right ScalarCore] [hl (ScalarScoped depth left)] [hr (ScalarScoped depth right)]
           :where [depth (ScalarCore.add left right)])
      (mul [depth Nat] [left ScalarCore] [right ScalarCore] [hl (ScalarScoped depth left)] [hr (ScalarScoped depth right)]
           :where [depth (ScalarCore.mul left right)])
      (let_ [depth Nat] [init ScalarCore] [body ScalarCore] [hi (ScalarScoped depth init)] [hb (ScalarScoped (Nat.succ depth) body)]
            :where [depth (ScalarCore.let_ init body)]))
    (a/defn scalarFiniteChecked [p :- ScalarCore] (=> (List Nat) (=> Nat (Option Nat)))
      (match p
        [(lit value) (fn [xs :- (List Nat), cap :- Nat] (scalarCheck value cap))]
        [(local index) (fn [xs :- (List Nat), cap :- Nat]
                         (scalarBind (scalarFiniteLookup xs index) (fn [v :- Nat] (scalarCheck v cap))))]
        [(add left right) (fn [xs :- (List Nat), cap :- Nat]
                           (scalarBind (scalarFiniteChecked left xs cap)
                             (fn [a :- Nat] (scalarBind (scalarFiniteChecked right xs cap)
                                             (fn [b :- Nat] (scalarCheck (+ a b) cap))))))]
        [(mul left right) (fn [xs :- (List Nat), cap :- Nat]
                           (scalarBind (scalarFiniteChecked left xs cap)
                             (fn [a :- Nat] (scalarBind (scalarFiniteChecked right xs cap)
                                             (fn [b :- Nat] (scalarCheck (* a b) cap))))))]
        [(let_ init body) (fn [xs :- (List Nat), cap :- Nat]
                           (scalarBind (scalarFiniteChecked init xs cap)
                             (fn [v :- Nat] (scalarFiniteChecked body (List.cons Nat v xs) cap))))]))
    (a/theorem scalar-bind-congr [answer :- (Option Nat), f :- (=> Nat (Option Nat)), g :- (=> Nat (Option Nat)),
                                    h :- (forall [value :- Nat] (= (Option Nat) (f value) (g value)))]
      (= (Option Nat) (scalarBind answer f) (scalarBind answer g))
      (cases answer) (all_goals (try (rfl))) (all_goals (exact (h val))))
    (a/theorem scalar-finite-checked [depth :- Nat, p :- ScalarCore, hs :- (ScalarScoped depth p)]
      (forall [xs :- (List Nat), length :- (= Nat (List.length xs) depth), cap :- Nat]
        (= (Option Nat) (scalarFiniteChecked p xs cap) (scalarChecked p (scalarFiniteEnv xs) cap)))
      (induction hs)
      (all_goals (intro xs) (intro length) (intro cap))
      (all_goals (simp only [scalarFiniteChecked scalarChecked]))
      (all_goals (try (rfl)))
      (all_goals (try (rw [(scalar-finite-lookup xs index (Eq.mpr (congrArg (fn [n :- Nat] (Nat.le (Nat.succ index) n)) length) within))])))
      (all_goals (simp only [scalarBind.eq_2]))
      (all_goals (try (rfl)))
      (all_goals (try (rw [(ih_hl xs length cap)])))
      (all_goals (try (rw [(ih_hr xs length cap)])))
      (all_goals (try (rfl)))
      (rw [(ih_hi xs length cap)])
      (exact (scalar-bind-congr (scalarChecked init (scalarFiniteEnv xs) cap)
               (fn [value :- Nat] (scalarFiniteChecked body (List.cons Nat value xs) cap))
               (fn [value :- Nat] (scalarChecked body (scalarPush value (scalarFiniteEnv xs)) cap))
               (fn [value :- Nat]
                 (Eq.trans (ih_hb (List.cons Nat value xs) (congrArg Nat.succ length) cap)
                           (congrArg (fn [rho :- (=> Nat Nat)] (scalarChecked body rho cap))
                                     (scalar-finite-push xs value)))))))
    (a/theorem scalar-finite-execution [depth :- Nat, p :- ScalarCore, hs :- (ScalarScoped depth p)]
      (forall [xs :- (List Nat), length :- (= Nat (List.length xs) depth), cap :- Nat]
        (And
          (= Bool (scalarCEKDone
                    (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt))
                                    (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt) cap)) true)
          (= (Option Nat)
             (scalarCEKMeaning
               (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt))
                               (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt) cap) cap)
             (scalarFiniteChecked p xs cap))))
      (intro xs) (intro length) (intro cap)
      (exact (And.intro
               (scalar-cek-terminates (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt) cap)
               (Eq.trans (scalar-cek-steps (scalarCEKCost (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt))
                                          (ScalarCEK.eval p (scalarFiniteEnv xs) ScalarKont.halt) cap)
                 (Eq.trans (scalar-cek-initial p (scalarFiniteEnv xs) cap)
                           (Eq.symm (scalar-finite-checked depth p hs xs length cap)))))))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "finite environment proof failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))


(defn scope-witness [body arity]
  (let [en @proof-state encoded (scalar/encode-body body arity)
        nat #(e/lit-nat (biginteger %))
        app (fn [name & args] (apply e/app* (k/c name) args))]
    (letfn [(go [t depth]
              (let [d (nat depth)]
                (case (:op t)
                  :quote {:core (app "ScalarCore.lit" (nat (:datum t)))
                          :proof (app "ScalarScoped.lit" d (nat (:datum t)))}
                  :local {:core (app "ScalarCore.local" (nat (:index t)))
                          :proof (app "ScalarScoped.local" d (nat (:index t))
                                      (app "Nat.le_of_ble_eq_true" (nat (inc (:index t))) d
                                           (e/app* (k/c "Eq.refl" [k/l1]) k/Bool (k/c "Bool.true"))))}
                  :let (let [a (go (:init t) depth) b (go (:body t) (inc depth))]
                         {:core (app "ScalarCore.let_" (:core a) (:core b))
                          :proof (app "ScalarScoped.let_" d (:core a) (:core b) (:proof a) (:proof b))})
                  :prim (let [[a b] (mapv #(go % depth) (:args t)) kind (if (= '+ (:name t)) "add" "mul")]
                          {:core (app (str "ScalarCore." kind) (:core a) (:core b))
                           :proof (app (str "ScalarScoped." kind) d (:core a) (:core b) (:proof a) (:proof b))}))))]
      (let [result (go body arity) goal (app "ScalarScoped" (nat arity) encoded)]
        (when-not (and (= encoded (:core result)) (env/verifies? en goal (:proof result)))
          (throw (ex-info "actual scalar scope proof rejected" {:reason :scope-proof})))
        {:source-id (c/code-id (c/lam arity body)) :arity arity :core encoded
         :goal goal :proof (:proof result) :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash (:proof result))}))))

(defn execution-witness [body arity]
  (let [scope (scope-witness body arity) core (:core scope)
        [xs length cap] (repeatedly 3 k/fvar!) vx (e/fvar xs) vc (e/fvar cap)
        length-type (k/eq k/Nat (e/app* (k/c "List.length" [k/l0]) k/Nat vx) (e/lit-nat (biginteger arity)))
        state (e/app* (k/c "ScalarCEK.eval") core (e/app (k/c "scalarFiniteEnv") vx) (k/c "ScalarKont.halt"))
        final (e/app* (k/c "scalarCEKSteps") (e/app (k/c "scalarCEKCost") state) state vc)
        goal (k/pi* [[xs "xs" (k/List k/Nat)] [length "length" length-type] [cap "cap" k/Nat]]
                    (e/app* (k/c "And")
                            (k/eq k/Bool (e/app (k/c "scalarCEKDone") final) (k/c "Bool.true"))
                            (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                                  (e/app* (k/c "scalarCEKMeaning") final vc)
                                  (e/app* (k/c "scalarFiniteChecked") core vx vc))))
        proof (e/app* (k/c "scalar-finite-execution") (e/lit-nat (biginteger arity)) core (:proof scope))]
    (when-not (env/verifies? @proof-state goal proof) (throw (ex-info "finite execution proof rejected" {:reason :finite-proof})))
    {:source-id (:source-id scope) :scope-witness scope :goal goal :proof proof
     :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
     :bridges [:Core-decoder :runtime-value-encoding :T0-implementation :Long-representation]}))

(defn verify-execution? [body arity receipt]
  (try
    (let [expected (execution-witness body arity)
          scope (:scope-witness receipt) expected-scope (:scope-witness expected)]
      (and (= (:source-id expected) (:source-id receipt))
           (= (select-keys expected-scope [:source-id :arity :core :goal :goal-sha256])
              (select-keys scope [:source-id :arity :core :goal :goal-sha256]))
           (= (:proof-sha256 scope) (k/expr-hash (:proof scope)))
           (env/verifies? @proof-state (:goal expected-scope) (:proof scope))
           (= (:goal expected) (:goal receipt))
           (= (:goal-sha256 receipt) (k/expr-hash (:goal expected)))
           (= (:proof-sha256 receipt) (k/expr-hash (:proof receipt)))
           (env/verifies? @proof-state (:goal expected) (:proof receipt))))
    (catch Exception _ false)))
