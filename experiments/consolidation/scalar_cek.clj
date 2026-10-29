(ns consolidation.scalar-cek
  "Defunctionalized scalar CEK frames and transition preservation. This model
   mirrors the admitted T0 frame shapes; the Clojure implementation/decoder
   remains a conformance boundary, not verified extraction."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm] [ansatz.kernel.expr :as e] [klara.fusion.kernel :as k] [consolidation.scalar-core :as scalar]))

(def theorem-names ["scalar-bind-assoc" "scalar-cek-eval-step" "scalar-cek-return-step"
                    "scalar-cek-step" "scalar-cek-steps"
                    "scalar-cost-positive" "scalar-cek-eval-cost" "scalar-cek-return-budget"
                    "scalar-budget-pred" "scalar-cek-step-budget" "scalar-next-budget"
                    "scalar-cek-steps-budget" "scalar-cek-zero-done"
                    "scalar-cek-terminates" "scalar-bind-pure" "scalar-cek-initial" "scalar-cek-bounded-execution"])
(defn prove! []
  (binding [*ns* (the-ns 'consolidation.scalar-cek)]
    (reset! a/ansatz-env @scalar/proof-state)
    (clojure.core/refer 'consolidation.scalar-core :only '[scalarChecked scalarBind scalarCheck scalarPush scalarMeaning])
    (a/inductive ScalarKont []
      (halt)
      (addLeft [right ScalarCore] [rho (=> Nat Nat)] [rest ScalarKont])
      (addRight [left Nat] [rest ScalarKont])
      (mulLeft [right ScalarCore] [rho (=> Nat Nat)] [rest ScalarKont])
      (mulRight [left Nat] [rest ScalarKont])
      (letBody [body ScalarCore] [rho (=> Nat Nat)] [rest ScalarKont]))
    (a/defn scalarKont [kont :- ScalarKont] (=> Nat (=> Nat (Option Nat)))
      (match kont
        [halt (fn [value :- Nat, cap :- Nat] (Option.some Nat value))]
        [(addLeft right rho rest)
         (fn [value :- Nat, cap :- Nat]
           (scalarBind (scalarChecked right rho cap)
             (fn [r :- Nat] (scalarBind (scalarCheck (+ value r) cap)
                             (fn [next :- Nat] (scalarKont rest next cap))))))]
        [(addRight left rest)
         (fn [value :- Nat, cap :- Nat]
           (scalarBind (scalarCheck (+ left value) cap) (fn [next :- Nat] (scalarKont rest next cap))))]
        [(mulLeft right rho rest)
         (fn [value :- Nat, cap :- Nat]
           (scalarBind (scalarChecked right rho cap)
             (fn [r :- Nat] (scalarBind (scalarCheck (* value r) cap)
                             (fn [next :- Nat] (scalarKont rest next cap))))))]
        [(mulRight left rest)
         (fn [value :- Nat, cap :- Nat]
           (scalarBind (scalarCheck (* left value) cap) (fn [next :- Nat] (scalarKont rest next cap))))]
        [(letBody body rho rest)
         (fn [value :- Nat, cap :- Nat]
           (scalarBind (scalarChecked body (scalarPush value rho) cap)
             (fn [next :- Nat] (scalarKont rest next cap))))]))
    (a/inductive ScalarCEK []
      (eval [p ScalarCore] [rho (=> Nat Nat)] [kont ScalarKont])
      (ret [answer (Option Nat)] [kont ScalarKont]))
    (a/defn scalarCEKMeaning [state :- ScalarCEK, cap :- Nat] (Option Nat)
      (match state
        [(eval p rho kont) (scalarBind (scalarChecked p rho cap) (fn [v :- Nat] (scalarKont kont v cap)))]
        [(ret answer kont) (scalarBind answer (fn [v :- Nat] (scalarKont kont v cap)))]))
    (a/defn scalarCEKEvalStep [p :- ScalarCore, rho :- (=> Nat Nat), kont :- ScalarKont, cap :- Nat] ScalarCEK
      (match p
        [(lit value) (ScalarCEK.ret (scalarCheck value cap) kont)]
        [(local index) (ScalarCEK.ret (scalarCheck (rho index) cap) kont)]
        [(add left right) (ScalarCEK.eval left rho (ScalarKont.addLeft right rho kont))]
        [(mul left right) (ScalarCEK.eval left rho (ScalarKont.mulLeft right rho kont))]
        [(let_ init body) (ScalarCEK.eval init rho (ScalarKont.letBody body rho kont))]))
    (a/defn scalarCEKReturnStep [kont :- ScalarKont, answer :- (Option Nat), cap :- Nat] ScalarCEK
      (match kont
        [halt (ScalarCEK.ret answer ScalarKont.halt)]
        [(addLeft right rho rest)
         (match answer [none (ScalarCEK.ret (Option.none Nat) rest)]
                       [(some value) (ScalarCEK.eval right rho (ScalarKont.addRight value rest))])]
        [(addRight left rest)
         (ScalarCEK.ret (scalarBind answer (fn [r :- Nat] (scalarCheck (+ left r) cap))) rest)]
        [(mulLeft right rho rest)
         (match answer [none (ScalarCEK.ret (Option.none Nat) rest)]
                       [(some value) (ScalarCEK.eval right rho (ScalarKont.mulRight value rest))])]
        [(mulRight left rest)
         (ScalarCEK.ret (scalarBind answer (fn [r :- Nat] (scalarCheck (* left r) cap))) rest)]
        [(letBody body rho rest)
         (match answer [none (ScalarCEK.ret (Option.none Nat) rest)]
                       [(some value) (ScalarCEK.eval body (scalarPush value rho) rest)])]))
    (a/theorem scalar-bind-assoc [answer :- (Option Nat), f :- (=> Nat (Option Nat)), g :- (=> Nat (Option Nat))]
      (= (Option Nat) (scalarBind (scalarBind answer f) g)
         (scalarBind answer (fn [v :- Nat] (scalarBind (f v) g))))
      (cases answer) (all_goals (rfl)))
    (a/theorem scalar-cek-eval-step [p :- ScalarCore, rho :- (=> Nat Nat), kont :- ScalarKont, cap :- Nat]
      (= (Option Nat) (scalarCEKMeaning (scalarCEKEvalStep p rho kont cap) cap)
         (scalarCEKMeaning (ScalarCEK.eval p rho kont) cap))
      (cases p)
      (all_goals (simp only [scalarCEKEvalStep scalarCEKMeaning scalarChecked
                             scalarKont scalar-bind-assoc])))
    (a/theorem scalar-cek-return-step [kont :- ScalarKont, answer :- (Option Nat), cap :- Nat]
      (= (Option Nat) (scalarCEKMeaning (scalarCEKReturnStep kont answer cap) cap)
         (scalarCEKMeaning (ScalarCEK.ret answer kont) cap))
      (cases kont)
      (all_goals (cases answer))
      (all_goals (simp only [scalarCEKReturnStep scalarCEKMeaning scalarBind scalarKont])))
    (a/defn scalarCEKStep [state :- ScalarCEK, cap :- Nat] ScalarCEK
      (match state
        [(eval p rho kont) (scalarCEKEvalStep p rho kont cap)]
        [(ret answer kont) (scalarCEKReturnStep kont answer cap)]))
    (a/defn scalarCEKSteps [fuel :- Nat] (=> ScalarCEK (=> Nat ScalarCEK))
      (match fuel
        [zero (fn [state :- ScalarCEK, cap :- Nat] state)]
        [(succ remaining) (fn [state :- ScalarCEK, cap :- Nat]
                            (scalarCEKSteps remaining (scalarCEKStep state cap) cap))]))
    (a/theorem scalar-cek-step [state :- ScalarCEK, cap :- Nat]
      (= (Option Nat) (scalarCEKMeaning (scalarCEKStep state cap) cap) (scalarCEKMeaning state cap))
      (cases state)
      (all_goals (simp only [scalarCEKStep]))
      (all_goals (try (exact (scalar-cek-eval-step p rho kont cap))))
      (all_goals (exact (scalar-cek-return-step kont answer cap))))
    (a/theorem scalar-cek-steps [fuel :- Nat]
      (forall [state :- ScalarCEK, cap :- Nat]
        (= (Option Nat) (scalarCEKMeaning (scalarCEKSteps fuel state cap) cap) (scalarCEKMeaning state cap)))
      (induction fuel)
      (all_goals (intro state) (intro cap))
      (all_goals (simp only [scalarCEKSteps.eq_1 scalarCEKSteps.eq_2]))
      (all_goals (try (rfl)))
      (exact (Eq.trans (ih_n (scalarCEKStep state cap) cap) (scalar-cek-step state cap))))
    (a/defn scalarCost [p :- ScalarCore] Nat
      (match p
        [(lit value) 1] [(local index) 1]
        [(add left right) (Nat.succ (Nat.succ (Nat.succ (+ (scalarCost left) (scalarCost right)))))]
        [(mul left right) (Nat.succ (Nat.succ (Nat.succ (+ (scalarCost left) (scalarCost right)))))]
        [(let_ init body) (Nat.succ (Nat.succ (+ (scalarCost init) (scalarCost body))))]))
    (a/defn scalarKontCost [kont :- ScalarKont] Nat
      (match kont
        [halt 0]
        [(addLeft right rho rest) (Nat.succ (Nat.succ (+ (scalarCost right) (scalarKontCost rest))))]
        [(addRight left rest) (Nat.succ (scalarKontCost rest))]
        [(mulLeft right rho rest) (Nat.succ (Nat.succ (+ (scalarCost right) (scalarKontCost rest))))]
        [(mulRight left rest) (Nat.succ (scalarKontCost rest))]
        [(letBody body rho rest) (Nat.succ (+ (scalarCost body) (scalarKontCost rest)))]))
    (a/defn scalarCEKCost [state :- ScalarCEK] Nat
      (match state [(eval p rho kont) (+ (scalarCost p) (scalarKontCost kont))]
                   [(ret answer kont) (scalarKontCost kont)]))
    (a/defn scalarCEKDone [state :- ScalarCEK] Bool
      (match state
        [(eval p rho kont) false]
        [(ret answer kont) (match kont [halt true] [(addLeft r rho rest) false]
                                     [(addRight l rest) false] [(mulLeft r rho rest) false]
                                     [(mulRight l rest) false] [(letBody b rho rest) false])]))
    (a/theorem scalar-cost-positive [p :- ScalarCore]
      (<= 1 (scalarCost p))
      (cases p) (all_goals (simp only [scalarCost])) (all_goals (omega)))
    (a/theorem scalar-cek-eval-cost [p :- ScalarCore, rho :- (=> Nat Nat), kont :- ScalarKont, cap :- Nat]
      (<= (Nat.succ (scalarCEKCost (scalarCEKEvalStep p rho kont cap)))
          (scalarCEKCost (ScalarCEK.eval p rho kont)))
      (cases p)
      (all_goals (simp only [scalarCEKEvalStep scalarCEKCost scalarCost scalarKontCost]))
      (all_goals (omega)))
    (a/theorem scalar-cek-return-budget [kont :- ScalarKont, answer :- (Option Nat), cap :- Nat]
      (<= (scalarCEKCost (scalarCEKReturnStep kont answer cap)) (Nat.pred (scalarKontCost kont)))
      (cases kont) (all_goals (cases answer))
      (all_goals (simp only [scalarCEKReturnStep scalarCEKReturnStep.eq_1 scalarCEKReturnStep.eq_2 scalarCEKReturnStep.eq_3 scalarCEKReturnStep.eq_4 scalarCEKReturnStep.eq_5 scalarCEKReturnStep.eq_6 scalarCEKCost scalarKontCost scalarBind Nat.pred_succ]))
      (all_goals (try (exact (Nat.le_refl _))))
      (all_goals (omega)))
    (a/theorem scalar-budget-pred [a :- Nat, b :- Nat, h :- (<= (Nat.succ a) b)]
      (<= a (Nat.pred b)) (cases b)
      (all_goals (simp only [Nat.pred_zero Nat.pred_succ])) (all_goals (omega)))
    (a/theorem scalar-cek-step-budget [state :- ScalarCEK, cap :- Nat]
      (<= (scalarCEKCost (scalarCEKStep state cap)) (Nat.pred (scalarCEKCost state)))
      (cases state) (all_goals (simp only [scalarCEKStep scalarCEKCost]))
      (all_goals (try (exact (scalar-budget-pred _ _ (scalar-cek-eval-cost p rho kont cap)))))
      (all_goals (exact (scalar-cek-return-budget kont answer cap))))
    (a/theorem scalar-next-budget [next :- Nat, before :- Nat, fuel :- Nat,
                                  hnext :- (<= next (Nat.pred before)), within :- (<= before (Nat.succ fuel))]
      (<= next fuel) (cases before)
      (all_goals (simp only [Nat.pred_zero Nat.pred_succ] at *)) (all_goals (omega)))
    (a/theorem scalar-cek-steps-budget [fuel :- Nat]
      (forall [state :- ScalarCEK, cap :- Nat, within :- (<= (scalarCEKCost state) fuel)]
        (= Nat (scalarCEKCost (scalarCEKSteps fuel state cap)) 0))
      (induction fuel)
      (all_goals (intro state) (intro cap) (intro within))
      (all_goals (simp only [scalarCEKSteps.eq_1 scalarCEKSteps.eq_2]))
      (all_goals (try (omega)))
      (exact (ih_n (scalarCEKStep state cap) cap
                   (scalar-next-budget _ _ n (scalar-cek-step-budget state cap) within))))
    (a/theorem scalar-cek-zero-done [state :- ScalarCEK, zero :- (= Nat (scalarCEKCost state) 0)]
      (= Bool (scalarCEKDone state) true)
      (cases state)
      (all_goals (try (cases p)))
      (all_goals (try (cases kont)))
      (all_goals (simp only [scalarCEKCost scalarKontCost scalarCost scalarCEKDone] at *))
      (all_goals (try (rfl)))
      (all_goals (omega)))
    (a/theorem scalar-cek-terminates [state :- ScalarCEK, cap :- Nat]
      (= Bool (scalarCEKDone (scalarCEKSteps (scalarCEKCost state) state cap)) true)
      (exact (scalar-cek-zero-done _
               (scalar-cek-steps-budget (scalarCEKCost state) state cap (Nat.le_refl (scalarCEKCost state))))))
    (a/theorem scalar-bind-pure [answer :- (Option Nat)]
      (= (Option Nat) (scalarBind answer (fn [value :- Nat] (Option.some Nat value))) answer)
      (cases answer) (all_goals (rfl)))
    (a/theorem scalar-cek-initial [p :- ScalarCore, rho :- (=> Nat Nat), cap :- Nat]
      (= (Option Nat) (scalarCEKMeaning (ScalarCEK.eval p rho ScalarKont.halt) cap) (scalarChecked p rho cap))
      (exact (scalar-bind-pure (scalarChecked p rho cap))))
    (a/theorem scalar-cek-bounded-execution
      [bounds :- (=> Nat Nat), cap :- Nat, p :- ScalarCore, upper :- Nat,
       h :- (ScalarBound cap bounds p upper)]
      (forall [rho :- (=> Nat Nat), henv :- (forall [i :- Nat] (<= (rho i) (bounds i)))]
        (And
          (= Bool (scalarCEKDone (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                                                (ScalarCEK.eval p rho ScalarKont.halt) cap)) true)
          (= (Option Nat)
             (scalarCEKMeaning (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                                               (ScalarCEK.eval p rho ScalarKont.halt) cap) cap)
             (Option.some Nat (scalarMeaning p rho)))))
      (intro rho) (intro henv)
      (exact (And.intro
               (scalar-cek-terminates (ScalarCEK.eval p rho ScalarKont.halt) cap)
               (Eq.trans (scalar-cek-steps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                                          (ScalarCEK.eval p rho ScalarKont.halt) cap)
                 (Eq.trans (scalar-cek-initial p rho cap)
                           (scalar-checked-sound bounds cap p upper h rho henv))))))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "scalar CEK theorem failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))


(defn execution-witness [body input-bounds]
  (let [en @proof-state scalar (scalar/certify-body body input-bounds)
        core (:core scalar) bounds (scalar/bounds-expression input-bounds)
        [rho i h] (repeatedly 3 k/fvar!)
        vr (e/fvar rho) cap (e/lit-nat (biginteger Long/MAX_VALUE))
        state (e/app* (k/c "ScalarCEK.eval") core vr (k/c "ScalarKont.halt"))
        final (e/app* (k/c "scalarCEKSteps") (e/app (k/c "scalarCEKCost") state) state cap)
        premises (k/pi* [[i "index" k/Nat]] (e/app* (k/c "Nat.le") (e/app vr (e/fvar i)) (e/app bounds (e/fvar i))))
        goal (k/pi* [[rho "rho" (k/arrow k/Nat k/Nat)] [h "bounded" premises]]
                    (e/app* (k/c "And")
                            (k/eq k/Bool (e/app (k/c "scalarCEKDone") final) (k/c "Bool.true"))
                            (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                                  (e/app* (k/c "scalarCEKMeaning") final cap)
                                  (e/app* (k/c "Option.some" [k/l0]) k/Nat
                                          (e/app* (k/c "scalarMeaning") core vr)))))
        proof (e/app* (k/c "scalar-cek-bounded-execution") bounds cap core
                      (e/lit-nat (biginteger (:upper scalar))) (:bound-proof scalar))]
    (when-not (env/verifies? en goal proof)
      (throw (ex-info "scalar CEK execution witness rejected" {:reason :cek-proof})))
    {:source-id (:source-id scalar) :scalar-witness scalar :goal goal :proof proof
     :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
     :bridges [:Core-decoder :finite-environment :T0-implementation :Long-representation]}))

(defn verify-execution? [body input-bounds receipt]
  (try
    (let [expected (execution-witness body input-bounds)]
      (and (= (:source-id expected) (:source-id receipt)) (= (:goal expected) (:goal receipt))
           (= (:goal-sha256 receipt) (k/expr-hash (:goal expected)))
           (= (:proof-sha256 receipt) (k/expr-hash (:proof receipt)))
           (scalar/verify-body-witness? body input-bounds (:scalar-witness receipt))
           (env/verifies? @proof-state (:goal expected) (:proof receipt))))
    (catch Exception _ false)))

(defn step-bound [body]
  (case (:op body)
    (:quote :local) 1
    :let (+ 2 (step-bound (:init body)) (step-bound (:body body)))
    :prim (+ 3 (step-bound (first (:args body))) (step-bound (second (:args body))))))

(defn observe
  "Independent handwritten frame machine over original Core. Pending is not a
   source failure. This is a differential implementation, not kernel extraction."
  [body args cap fuel]
  (scalar/encode-body body (count args))
  (let [check (fn [value] (if (<= 0 value cap) [:ok (long value)] [:overflow]))]
    (loop [state {:tag :eval :term body :locals (vec args) :kont []} fuel fuel steps 0]
      (if (or (and (= :ret (:tag state)) (empty? (:kont state))) (zero? fuel))
        {:status (if (= :ret (:tag state)) (if (empty? (:kont state)) :done :pending) :pending)
         :answer (:answer state) :steps steps :remaining fuel}
        (let [{:keys [tag term locals kont answer]} state
              next-state
              (if (= :eval tag)
                (case (:op term)
                  :quote {:tag :ret :answer (check (:datum term)) :kont kont}
                  :local {:tag :ret :answer (check (nth locals (- (count locals) 1 (:index term)))) :kont kont}
                  :let {:tag :eval :term (:init term) :locals locals
                        :kont (conj kont {:tag :let :body (:body term) :locals locals})}
                  :prim {:tag :eval :term (first (:args term)) :locals locals
                         :kont (conj kont {:tag :left :op (:name term) :right (second (:args term)) :locals locals})})
                (let [frame (peek kont) rest (pop kont)]
                  (if (not= :ok (first answer)) {:tag :ret :answer answer :kont rest}
                    (case (:tag frame)
                      :let {:tag :eval :term (:body frame) :locals (conj (:locals frame) (second answer)) :kont rest}
                      :left {:tag :eval :term (:right frame) :locals (:locals frame)
                             :kont (conj rest {:tag :right :op (:op frame) :left (second answer)})}
                      :right {:tag :ret :answer (check ((case (:op frame) + +' * *') (:left frame) (second answer))) :kont rest}))))]
          (recur next-state (dec fuel) (inc steps)))))))
