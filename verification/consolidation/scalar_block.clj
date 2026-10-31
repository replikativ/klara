(ns consolidation.scalar-block
 "Per-source refinement of restricted scalar Core to ordered fresh slots.
  Nat/cap models are kernel checked; hosted decoding/emission remain bridges."
 (:require [ansatz.core :as a] [consolidation.scalar-finite :as finite]
           [consolidation.scalar-core :as scalar] [consolidation.scalar-cek :as cek]
           [ansatz.kernel.expr :as e] [ansatz.kernel.env :as env]
           [ansatz.tactic.proof :as proof] [ansatz.tactic.basic :as basic]
           [ansatz.tactic.simp :as simp]
           [ansatz.tactic.extract :as extract] [klara.fusion.kernel :as k]
           [klara.core :as core]))
(defn model! []
 (binding [*ns* (the-ns 'consolidation.scalar-block)]
(reset! a/ansatz-env @finite/proof-state)
(clojure.core/refer 'consolidation.scalar-core :only '[scalarCheck scalarChecked scalarBind scalarPush])
(a/defn slotStore [slots :- (=> Nat Nat), index :- Nat, value :- Nat, query :- Nat] Nat
 (match (Nat.beq query index) [true value] [false (slots query)]))
(a/inductive SlotBlock []
 (ret [slot Nat])
 (literal [target Nat] [value Nat] [rest SlotBlock])
 (copy [target Nat] [source Nat] [rest SlotBlock])
 (add [target Nat] [left Nat] [right Nat] [rest SlotBlock])
 (mul [target Nat] [left Nat] [right Nat] [rest SlotBlock]))
(a/defn slotRun [p :- SlotBlock] (=> (=> Nat Nat) (=> Nat (Option Nat)))
 (match p
  [(ret slot) (fn [slots :- (=> Nat Nat), cap :- Nat] (Option.some Nat (slots slot)))]
  [(literal target value rest) (fn [slots :- (=> Nat Nat), cap :- Nat]
    (scalarBind (scalarCheck value cap) (fn [v :- Nat] (slotRun rest (slotStore slots target v) cap))))]
  [(copy target source rest) (fn [slots :- (=> Nat Nat), cap :- Nat]
    (scalarBind (scalarCheck (slots source) cap) (fn [v :- Nat] (slotRun rest (slotStore slots target v) cap))))]
  [(add target left right rest) (fn [slots :- (=> Nat Nat), cap :- Nat]
    (scalarBind (scalarCheck (+ (slots left) (slots right)) cap) (fn [v :- Nat] (slotRun rest (slotStore slots target v) cap))))]
  [(mul target left right rest) (fn [slots :- (=> Nat Nat), cap :- Nat]
    (scalarBind (scalarCheck (* (slots left) (slots right)) cap) (fn [v :- Nat] (slotRun rest (slotStore slots target v) cap))))]))

 (a/theorem slot-block-cek
  [p :- ScalarCore, block :- SlotBlock,
   refinement :- (forall [rho :- (=> Nat Nat), cap :- Nat]
                    (= (Option Nat) (slotRun block rho cap) (scalarChecked p rho cap)))]
  (forall [rho :- (=> Nat Nat), cap :- Nat]
   (And
    (= Bool (scalarCEKDone
             (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                            (ScalarCEK.eval p rho ScalarKont.halt) cap)) true)
    (= (Option Nat)
       (scalarCEKMeaning
        (scalarCEKSteps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                       (ScalarCEK.eval p rho ScalarKont.halt) cap) cap)
       (slotRun block rho cap))))
  (intro rho) (intro cap)
  (exact (And.intro
           (scalar-cek-terminates (ScalarCEK.eval p rho ScalarKont.halt) cap)
           (Eq.trans
             (scalar-cek-steps (scalarCEKCost (ScalarCEK.eval p rho ScalarKont.halt))
                              (ScalarCEK.eval p rho ScalarKont.halt) cap)
             (Eq.trans (scalar-cek-initial p rho cap) (Eq.symm (refinement rho cap)))))))
 (a/env)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (model!))))

(defn lower
  "Fresh-slot, left-to-right lowering of the existing restricted scalar Core.
   This is an experimental block artifact, not another runtime interpreter."
  [body arity]
  (scalar/encode-body body arity)
  (letfn [(go [t locals next-slot]
            (case (:op t)
              :quote {:instructions [[:literal next-slot (:datum t)]]
                      :result next-slot :next (inc next-slot)}
              :local {:instructions [[:copy next-slot (nth locals (:index t))]]
                      :result next-slot :next (inc next-slot)}
              :let (let [a (go (:init t) locals next-slot)
                         b (go (:body t) (into [(:result a)] locals) (:next a))]
                     (update b :instructions #(into (:instructions a) %)))
              :prim (let [[left right] (:args t) a (go left locals next-slot)
                          b (go right locals (:next a)) target (:next b)]
                      {:instructions (conj (into (:instructions a) (:instructions b))
                                           [(if (= '+ (:name t)) :add :mul)
                                            target (:result a) (:result b)])
                       :result target :next (inc target)})))]
    (assoc (go body (vec (range arity)) arity) :arity arity)))

(defn- nat [n] (e/lit-nat (biginteger n)))
(defn- app [name & args] (apply e/app* (k/c name) args))

(defn encode-block
  "Validate initialized reads and monotonically fresh writes before encoding."
  [{:keys [arity instructions result next] :as block}]
  (when-not (and (= (set (keys block)) #{:arity :instructions :result :next})
                 (integer? arity) (<= 0 arity) (vector? instructions))
    (throw (ex-info "Invalid block interface" {:reason :block-interface})))
  (let [initialized
        (reduce (fn [expected [op target & args :as instruction]]
                  (when-not (and (= target expected)
                                 (case op
                                   :literal (and (= 3 (count instruction))
                                                 (instance? Long (first args))
                                                 (<= 0 (first args)))
                                   :copy (and (= 3 (count instruction))
                                              (every? #(and (integer? %) (<= 0 % (dec expected))) args))
                                   (:add :mul) (and (= 4 (count instruction))
                                                    (every? #(and (integer? %) (<= 0 % (dec expected))) args))
                                   false))
                    (throw (ex-info "Invalid fresh-slot instruction" {:instruction instruction})))
                  (inc expected)) arity instructions)]
    (when-not (and (= next initialized) (integer? result) (<= 0 result (dec initialized)))
      (throw (ex-info "Invalid block result" {:reason :block-result})))
    (reduce (fn [rest [op target & args]]
              (apply app (str "SlotBlock." (name op)) (concat (map nat (cons target args)) [rest])))
            (app "SlotBlock.ret" (nat result)) (rseq instructions))))

(defn goal-for [body arity block]
  (when-not (= arity (:arity block))
    (throw (ex-info "Block arity mismatch" {:reason :block-arity})))
  (let [source (scalar/encode-body body arity) target (encode-block block)
        [rho cap] (repeatedly 2 k/fvar!) vr (e/fvar rho) vc (e/fvar cap)]
    (k/pi* [[rho "rho" (k/arrow k/Nat k/Nat)] [cap "cap" k/Nat]]
           (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                 (app "slotRun" target vr vc) (app "scalarChecked" source vr vc)))))

(defn execution-goal-for [body arity block]
  (let [source (scalar/encode-body body arity) target (encode-block block)
        [rho cap] (repeatedly 2 k/fvar!) vr (e/fvar rho) vc (e/fvar cap)
        state (app "ScalarCEK.eval" source vr (k/c "ScalarKont.halt"))
        final (app "scalarCEKSteps" (app "scalarCEKCost" state) state vc)]
    (k/pi* [[rho "rho" (k/arrow k/Nat k/Nat)] [cap "cap" k/Nat]]
      (app "And" (k/eq k/Bool (app "scalarCEKDone" final) (k/c "Bool.true"))
           (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                 (app "scalarCEKMeaning" final vc) (app "slotRun" target vr vc))))))

(defn certify
  "Construct and independently check a per-source universal refinement proof.
   This validates the encoded block; it is not a universal lowering theorem or
   proof of the Clojure emitter, decoder, arrays, closures or full T0."
  ([body arity] (certify body arity (lower body arity)))
  ([body arity block]
   (let [en @proof-state goal (goal-for body arity block)
         [ps _] (proof/start-proof en goal)
         ps (basic/intros ps ["rho" "cap"])
         ;; dsimp computes concrete slot addresses under binders. Associativity
         ;; then exposes the same ordered checks as the tree evaluator.
         simplify #(simp/simp % '[slotRun slotStore scalarChecked scalarPush scalar-bind-assoc scalar-bind-pure]
                              {:only? true :max-depth 256})
         tactics [simplify simp/dsimp]
         ps (reduce (fn [state tactic]
                      (if (proof/solved? state) (reduced state)
                        (try (tactic state)
                             (catch clojure.lang.ExceptionInfo ex
                               (if (re-find #"made no progress" (.getMessage ex)) state (throw ex))))))
                    ps (take (* 2 (+ 2 (count (:instructions block)))) (cycle tactics)))]
     (when-not (proof/solved? ps)
       (throw (ex-info "Block refinement proof incomplete" {:goals (proof/format-goals ps)})))
     (extract/verify ps)
     (let [p (extract/extract ps)
           execution-goal (execution-goal-for body arity block)
           execution-proof (app "slot-block-cek" (scalar/encode-body body arity)
                                (encode-block block) p)]
       (when-not (and (env/verifies? en goal p)
                      (env/verifies? en execution-goal execution-proof))
         (throw (ex-info "Block refinement rejected" {:reason :block-proof})))
       {:source-id (core/code-id (core/lam arity body)) :arity arity :block block
        :goal goal :proof p :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash p)
        :execution-goal execution-goal :execution-proof execution-proof
        :bridges [:Core-decoder :input-slot-encoding :T0-implementation :JVM-emission]}))))

(defn verify? [body arity receipt]
  (try
    (let [goal (goal-for body arity (:block receipt))]
      (and (= arity (:arity receipt))
           (= (core/code-id (core/lam arity body)) (:source-id receipt))
           (= goal (:goal receipt))
           (= (k/expr-hash goal) (:goal-sha256 receipt))
           (= (k/expr-hash (:proof receipt)) (:proof-sha256 receipt))
           (= (execution-goal-for body arity (:block receipt)) (:execution-goal receipt))
           (env/verifies? @proof-state goal (:proof receipt))
           (env/verifies? @proof-state (:execution-goal receipt) (:execution-proof receipt))))
    (catch Exception _ false)))

(def ^:private primitive-anchors {'+ clojure.core/+ '* clojure.core/*})

(defn emit-long
  "Small hosted bridge for inspecting the proven block as JVM-compiled Clojure.
   Only nonnegative Long inputs, cap=Long/MAX_VALUE, and anchored primitives.
   Admission failure declines; there is no fallback or interior recovery here."
  [body arity receipt]
  (when-not (verify? body arity receipt)
    (throw (ex-info "Invalid refinement receipt" {:reason :block-proof})))
  (when (> arity 20)
    (throw (ex-info "Hosted emitter supports at most 20 arguments" {:reason :host-arity})))
  (let [block (:block receipt) arg #(symbol (str "arg" %)) slot #(symbol (str "slot" %))
        check-roots! (fn []
                       (doseq [[name f] primitive-anchors]
                         (when-not (identical? f (get core/prims name))
                           (throw (ex-info "Changed scalar primitive" {:reason :primitive-context})))))
        bindings (into (vec (mapcat (fn [i] [(slot i) (list 'clojure.core/long (arg (- arity 1 i)))])
                                    (range arity)))
                       (mapcat (fn [[op target a b]]
                                 [(slot target)
                                  (case op
                                    :literal (list 'clojure.core/long a)
                                    :copy (slot a)
                                    :add (list 'clojure.core/+ (slot a) (slot b))
                                    :mul (list 'clojure.core/* (slot a) (slot b)))])
                               (:instructions block)))
        form (list 'fn (mapv arg (range arity))
                   (list 'let bindings (slot (:result block))))
        _ (check-roots!)
        executable (binding [*unchecked-math* false] (eval form))]
    {:form form :receipt receipt
     :invoke (fn [& args]
               (check-roots!)
               (when-not (and (= arity (count args))
                              (every? #(and (instance? Long %) (<= 0 %)) args))
                 (throw (ex-info "Scalar entry declined" {:reason :input-layout})))
               (apply executable args))}))
