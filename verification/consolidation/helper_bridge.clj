(ns consolidation.helper-bridge
  "Semantic witnesses for actual closed singleton-vector helper bodies.
   Reification is structural and fail-closed; correspondence of this small
   semantics to T0/JVM execution remains an explicit bridge."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [consolidation.private-state :as private]
            [klara.core :as c]
            [klara.fusion.kernel :as k]))

(defn definitions! []
  (binding [*ns* (the-ns 'consolidation.helper-bridge)]
    ;; Extend a checked immutable model environment, preserving its theorem
    ;; bodies and exact imported foundation rather than postulating them.
    (reset! a/ansatz-env (:environment @private/proof-state))
    (a/inductive HelperValue [] (nat [n Nat]) (box [v HelperValue]))
    (a/inductive HelperResult [] (ok [v HelperValue]) (error [category Nat]))
    (a/inductive HelperTerm []
      (local [index Nat]) (lit [n Nat]) (box [v HelperTerm])
      (read [v HelperTerm]) (bump [v HelperTerm])
      (put [base HelperTerm] [v HelperTerm])
      (let_ [init HelperTerm] [body HelperTerm])
      (branch [test Bool] [left HelperTerm] [right HelperTerm])
      (call [callee HelperTerm] [argument HelperTerm]))
    (a/defn helperBind [r :- HelperResult, f :- (=> HelperValue HelperResult)] HelperResult
      (match r [(ok v) (f v)] [(error category) (HelperResult.error category)]))
    (a/defn helperRead [v :- HelperValue] HelperResult
      (match v [(nat n) (HelperResult.error 2)] [(box value) (HelperResult.ok value)]))
    (a/defn helperNatBump [n :- Nat, cap :- Nat] HelperResult
      (match (Nat.blt n cap)
        [true (HelperResult.ok (HelperValue.nat (+ n 1)))] [false (HelperResult.error 0)]))
    (a/defn helperBump [v :- HelperValue] (=> Nat HelperResult)
      (match v
        [(nat n) (fn [cap :- Nat] (helperNatBump n cap))]
        [(box value) (fn [cap :- Nat] (HelperResult.error 2))]))
    (a/defn helperPut [base :- HelperValue, v :- HelperValue] HelperResult
      (match base [(nat n) (HelperResult.error 2)] [(box old) (HelperResult.ok (HelperValue.box v))]))
    (a/defn helperLookup [values :- (List HelperValue)] (=> Nat HelperResult)
      (match values
        [nil (fn [index :- Nat] (HelperResult.error 3))]
        [(cons value rest)
         (fn [index :- Nat]
           (match index [zero (HelperResult.ok value)] [(succ previous) (helperLookup rest previous)]))]))
    (a/defn helperEval [p :- HelperTerm] (=> (List HelperValue) (=> Nat HelperResult))
      (match p
        [(local index) (fn [values :- (List HelperValue), cap :- Nat] (helperLookup values index))]
        [(lit n) (fn [values :- (List HelperValue), cap :- Nat] (HelperResult.ok (HelperValue.nat n)))]
        [(box value)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval value values cap)
                       (fn [v :- HelperValue] (HelperResult.ok (HelperValue.box v)))))]
        [(read value)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval value values cap) helperRead))]
        [(bump value)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval value values cap) (fn [v :- HelperValue] (helperBump v cap))))]
        [(put base value)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval base values cap)
             (fn [b :- HelperValue]
               (helperBind (helperEval value values cap) (fn [v :- HelperValue] (helperPut b v))))))]
        [(let_ init body)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval init values cap)
             (fn [v :- HelperValue] (helperEval body (List.cons HelperValue v values) cap))))]
        [(branch test left right)
         (fn [values :- (List HelperValue), cap :- Nat]
           (match test [true (helperEval left values cap)] [false (helperEval right values cap)]))]
        [(call callee argument)
         (fn [values :- (List HelperValue), cap :- Nat]
           (helperBind (helperEval argument values cap)
             (fn [value :- HelperValue]
               (helperEval callee (List.cons HelperValue value (List.nil HelperValue)) cap))))]))
    ;; Keeping the partial operation under bind makes its failure order explicit.
    (a/defn helperStep [x :- Nat, cap :- Nat] HelperResult
      (helperBind (helperBump (HelperValue.nat x) cap)
                  (fn [v :- HelperValue] (HelperResult.ok (HelperValue.box v)))))
    (a/defn helperLoop [n :- Nat] (=> HelperTerm (=> HelperValue (=> Nat HelperResult)))
      (match n
        [zero (fn [p :- HelperTerm, value :- HelperValue, cap :- Nat] (HelperResult.ok value))]
        [(succ previous)
         (fn [p :- HelperTerm, value :- HelperValue, cap :- Nat]
           (helperBind (helperEval p (List.cons HelperValue value (List.nil HelperValue)) cap)
                       (fn [v :- HelperValue] (helperLoop previous p v cap))))]))
    (a/defn helperReference [n :- Nat] (=> HelperValue (=> Nat HelperResult))
      (match n
        [zero (fn [value :- HelperValue, cap :- Nat] (HelperResult.ok value))]
        [(succ previous)
         (fn [value :- HelperValue, cap :- Nat]
           (helperBind (helperRead value)
             (fn [scalar :- HelperValue]
               (helperBind (helperBump scalar cap)
                 (fn [next :- HelperValue]
                   (helperReference previous (HelperValue.box next) cap))))))]))
    ;; The compositional contract is universal over input values. It includes
    ;; type failures, so the induction need not assume a successful last step.
    (a/theorem helper-loop-substitution
      [p :- HelperTerm,
       contract :- (forall [value :- HelperValue, cap :- Nat]
                     (= HelperResult
                        (helperEval p (List.cons HelperValue value (List.nil HelperValue)) cap)
                        (helperBind (helperRead value)
                          (fn [scalar :- HelperValue]
                            (helperBind (helperBump scalar cap)
                              (fn [next :- HelperValue] (HelperResult.ok (HelperValue.box next))))))))]
      (forall [n :- Nat, value :- HelperValue, cap :- Nat]
        (= HelperResult (helperLoop n p value cap) (helperReference n value cap)))
      (intro n) (induction n)
      (all_goals (intro value) (intro cap))
      (all_goals (simp only [helperLoop.eq_1 helperLoop.eq_2 helperReference.eq_1 helperReference.eq_2]))
      (all_goals (try (rfl)))
      (rw [(contract value cap)])
      (cases value)
      (all_goals (simp only [helperRead helperBind helperBump helperNatBump]))
      (all_goals (try (rfl)))
      (cases v)
      (all_goals (simp only [helperBump helperNatBump helperBind]))
      (all_goals (try (rfl)))
      (all_goals (try (split_ifs)))
      (all_goals (try (rw [hc])))
      (all_goals (try (rfl)))
      (all_goals (try (apply ih_n))))
    (a/defn helperPrivate [answer :- PrivateAnswer] HelperResult
      (match answer
        [(ok value history outside) (HelperResult.ok (HelperValue.box (HelperValue.nat value)))]
        [(error category outside) (HelperResult.error category)]))
    (a/defn helperPrivateExit [exit :- PrivateExit] HelperResult
      (match exit [(mk answer released) (helperPrivate answer)]))
    (a/theorem helper-reference-private [n :- Nat]
      (forall [x :- Nat, cap :- Nat]
        (= HelperResult
           (helperReference n (HelperValue.box (HelperValue.nat x)) cap)
           (helperPrivate (privateSource (privateRepeat n) x (List.nil Nat) (List.nil Nat) cap))))
      (induction n)
      (all_goals (intro x) (intro cap))
      (all_goals (simp only [helperReference.eq_1 helperReference.eq_2
                            privateRepeat.eq_1 privateRepeat.eq_2 privateSource.eq_1 privateSource.eq_2
                            helperRead helperBump helperNatBump helperBind helperPrivate]))
      (all_goals (simp only [helperRead.eq_2 helperBump.eq_1 helperBind.eq_1
                            helperPrivate.eq_1 helperPrivate.eq_2 helperNatBump]))
      (all_goals (try (rfl)))
      (all_goals (try (split_ifs)))
      (all_goals (try (rw [hc])))
      (all_goals (try (rfl)))
      (all_goals (try (exact (ih_n (+ x 1) cap)))))
    (a/theorem helper-private-composition
      [p :- HelperTerm,
       contract :- (forall [value :- HelperValue, cap :- Nat]
                     (= HelperResult
                        (helperEval p (List.cons HelperValue value (List.nil HelperValue)) cap)
                        (helperBind (helperRead value)
                          (fn [scalar :- HelperValue]
                            (helperBind (helperBump scalar cap)
                              (fn [next :- HelperValue] (HelperResult.ok (HelperValue.box next))))))))]
      (forall [n :- Nat, x :- Nat, cap :- Nat]
        (= HelperResult
           (helperLoop n p (HelperValue.box (HelperValue.nat x)) cap)
           (helperPrivateExit
             (privateTarget (privateRepeat n) (PrivateCell.mk x) (List.nil Nat) 0 (List.nil Nat) cap))))
      (intro n) (intro x) (intro cap)
      (rw [(private-state-simulation (privateRepeat n) (private-repeat-safe n)
                                    x (List.nil Nat) (List.nil Nat) cap)])
      (simp only [helperPrivateExit])
      (exact (Eq.trans (helper-loop-substitution p contract n (HelperValue.box (HelperValue.nat x)) cap)
                        (helper-reference-private n x cap))))
    (a/theorem helper-counter-index-safe
      [n :- Nat, i :- Nat, cap :- Nat, hn :- (<= n cap), hi :- (< i n)]
      (<= (+ i 1) cap)
      (omega))
    (let [en (a/env)]
      (doseq [name ["helper-loop-substitution" "helper-reference-private"
                    "helper-private-composition" "helper-counter-index-safe"]
              :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "helper bridge theorem failed independent checking" {:theorem name}))))
      en)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (definitions!))))

(defn reify-body [source]
  (c/assert-wf! source)
  (when-not (and (= :fn (:op source)) (= 1 (:arity source)) (not (:rest? source)))
    (throw (ex-info "helper proof requires a closed unary function" {:reason :helper-interface})))
  (letfn [(go [t]
            (case (:op t)
              :local (e/app (k/c "HelperTerm.local") (e/lit-nat (:index t)))
              :quote (let [x (:datum t)]
                       (if (and (instance? Long x) (<= 0 x))
                         (e/app (k/c "HelperTerm.lit") (e/lit-nat (biginteger x)))
                         (throw (ex-info "unsupported helper proof literal" {:reason :helper-literal}))))
              :let (e/app* (k/c "HelperTerm.let_") (go (:init t)) (go (:body t)))
              :if (if (and (= :quote (get-in t [:test :op])) (boolean? (get-in t [:test :datum])))
                    (e/app* (k/c "HelperTerm.branch")
                            (k/c (if (get-in t [:test :datum]) "Bool.true" "Bool.false"))
                            (go (:then t)) (go (:else t)))
                    (throw (ex-info "unsupported helper proof condition" {:reason :helper-condition})))
              :prim
              (let [args (:args t)]
                (case [(:name t) (count args)]
                  [vector 1] (e/app (k/c "HelperTerm.box") (go (first args)))
                  [inc 1] (e/app (k/c "HelperTerm.bump") (go (first args)))
                  [nth 2] (if (= (c/quote* 0) (second args))
                            (e/app (k/c "HelperTerm.read") (go (first args)))
                            (throw (ex-info "only slot zero is in the helper proof fragment" {:reason :helper-index})))
                  [assoc 3] (if (= (c/quote* 0) (second args))
                              (e/app* (k/c "HelperTerm.put") (go (first args)) (go (nth args 2)))
                              (throw (ex-info "only slot zero is in the helper proof fragment" {:reason :helper-index})))
                  (throw (ex-info "unsupported helper proof primitive" {:reason :helper-operation}))))
              (throw (ex-info "unsupported helper proof operation" {:reason :helper-effect}))))]
    (go (:body source))))

(defn witness-term
  ([term source-id] (witness-term term source-id :vector-step))
  ([term source-id relation]
  (when-not (contains? #{:vector-step :scalar-step} relation)
    (throw (ex-info "unknown helper semantic contract" {:reason :helper-contract})))
  (let [en @proof-state
        [v cap] (repeatedly 2 k/fvar!) vv (e/fvar v) vc (e/fvar cap)
        value-type (k/c "HelperValue") result-type (k/c "HelperResult")
        ;; Generic contract preserves the actual scalar type-failure order.
        [scalar next] (repeatedly 2 k/fvar!)
        box (fn [v] (e/app (k/c "HelperValue.box") v))
        ok (fn [v] (e/app (k/c "HelperResult.ok") v))
        expected
        (fn [vv vc]
          (e/app* (k/c "helperBind") (e/app (k/c "helperRead") vv)
            (k/lam* [[scalar "scalar" value-type]]
              (if (= :scalar-step relation)
                (e/app* (k/c "helperBump") (e/fvar scalar) vc)
                (e/app* (k/c "helperBind") (e/app* (k/c "helperBump") (e/fvar scalar) vc)
                  (k/lam* [[next "next" value-type]] (ok (box (e/fvar next)))))))))
        actual (fn [vv vc]
                 (let [values (e/app* (k/c "List.cons" [k/l0]) value-type vv
                                      (e/app (k/c "List.nil" [k/l0]) value-type))]
                   (e/app* (k/c "helperEval") term values vc)))
        at (fn [vv] (k/pi* [[cap "cap" k/Nat]] (k/eq result-type (actual vv vc) (expected vv vc))))
        goal (k/pi* [[v "value" value-type]] (at vv))
        [n inner] (repeatedly 2 k/fvar!)
        branch (fn [id name type value]
                 (k/lam* [[id name type] [cap "cap" k/Nat]]
                   (e/app* (k/c "Eq.refl" [k/l1]) result-type (expected value vc))))
        proof (k/lam* [[v "value" value-type]]
                (e/app* (k/c "HelperValue.casesOn" [k/l0])
                  (k/lam* [[v "value" value-type]] (at vv)) vv
                  (branch n "n" k/Nat (e/app (k/c "HelperValue.nat") (e/fvar n)))
                  (branch inner "inner" value-type (box (e/fvar inner)))))]
    (when-not (env/verifies? en goal proof)
      (throw (ex-info "helper body does not establish the requested step contract"
                      {:reason :helper-proof :source-id source-id})))
    (cond-> {:source-id source-id :relation relation :term term :goal goal :proof proof
     :environment en :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}
      (= :vector-step relation)
      (assoc :loop-proof (e/app* (k/c "helper-loop-substitution") term proof)
             :private-proof (e/app* (k/c "helper-private-composition") term proof))))))

(defn witness
  ([source] (witness source :vector-step))
  ([source relation]
   (assoc (witness-term (reify-body source) (c/code-id source) relation) :source source)))

(defn private-goal [term]
  (let [[n x cap] (repeatedly 3 k/fvar!) [vn vx vc] (map e/fvar [n x cap])
        nil-nat (e/app (k/c "List.nil" [k/l0]) k/Nat)]
    (k/pi* [[n "iterations" k/Nat] [x "value" k/Nat] [cap "cap" k/Nat]]
      (k/eq (k/c "HelperResult")
        (e/app* (k/c "helperLoop") vn term
                (e/app (k/c "HelperValue.box") (e/app (k/c "HelperValue.nat") vx)) vc)
        (e/app (k/c "helperPrivateExit")
          (e/app* (k/c "privateTarget") (e/app (k/c "privateRepeat") vn)
                  (e/app (k/c "PrivateCell.mk") vx) nil-nat (e/lit-nat 0) nil-nat vc))))))

(defn verify-witness?
  ([source receipt] (verify-witness? source :vector-step receipt))
  ([source relation receipt]
  (try
    (let [expected (witness source relation) en @proof-state]
      (and (= relation (:relation receipt)) (= (c/code-id source) (:source-id receipt))
           (= (:term expected) (:term receipt))
           (env/verifies? en (:goal expected) (:proof receipt))
           (or (= :scalar-step relation)
               (env/verifies? en (private-goal (:term expected)) (:private-proof receipt)))))
    (catch Exception _ false))))

(defn verify-term-witness? [term source-id receipt]
  (try
    (let [expected (witness-term term source-id) en @proof-state]
      (and (= source-id (:source-id receipt)) (= term (:term receipt))
           (= :vector-step (:relation receipt))
           (env/verifies? en (:goal expected) (:proof receipt))
           (env/verifies? en (private-goal term) (:private-proof receipt))))
    (catch Exception _ false)))
