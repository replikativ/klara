(ns consolidation.counted-core
  "Independent decoder for a singleton scalar strict-fold lowering. This binds
   actual Core endpoints to the kernel indexed-driver model; decoder/CEK/Long
   adequacy is tested, not a theorem about the entire T0 implementation."
  (:require [consolidation.scalar-core :as scalar]
            [consolidation.scalar-driver :as driver]
            [consolidation.scalar-sum :as sum]
            [ansatz.kernel.expr :as e] [ansatz.kernel.env :as env]
            [klara.core :as c] [klara.fusion.kernel :as k]))

(defn- reject! [check]
  (throw (ex-info "unsupported counted Core correspondence" {:reason :counted-core :check check})))
(defn- same-code? [a b] (= (c/code-id a) (c/code-id b)))
(defn- host-call? [node op n]
  (and (= :perform (:op node)) (nil? (:target node)) (= :host/call (:name node))
       (= n (count (:args node))) (= (c/quote* op) (first (:args node)))))

(defn inspect-source [source]
  (c/assert-wf! source)
  (let [body (:body source) [_ f init input] (:args body)
        prefix? (host-call? input 'clojure.core/take 3)
        prefix (when prefix? (get-in input [:args 1 :datum]))
        xs (if prefix? (get-in input [:args 2]) input)
        seed (:datum init)
        step (if (and (= :fn (:op f)) (= 2 (:arity f)) (not (:rest? f)))
               (:body f)
               (when (and (= :perform (:op f)) (nil? (:target f)) (= :host/var (:name f))
                          (= 1 (count (:args f)))
                          (#{'clojure.core/+ 'clojure.core/*} (get-in f [:args 0 :datum])))
                 (c/prim (symbol (name (get-in f [:args 0 :datum]))) (c/local 1) (c/local 0))))]
    (when-not (and (= :fn (:op source)) (= 1 (:arity source)) (not (:rest? source))
                   (host-call? body 'clojure.core/reduce 4)
                   (= :quote (:op init)) (instance? Long seed) (<= 0 seed)
                   (= xs (c/local 0)) step
                   (or (not prefix?) (and (instance? Long prefix) (<= 0 prefix))))
      (reject! :source))
    (scalar/encode-body step 2)
    {:step step :seed seed :prefix prefix} ))

(defn- decode-step [t depth]
  (cond
    (same-code? t (c/prim 'nth (c/local (inc depth)) (c/quote* 0))) (c/local (inc depth))
    (= :local (:op t)) (if (<= (:index t) depth) t (reject! :step-local))
    (= :quote (:op t)) t
    (= :let (:op t)) (c/let1 (decode-step (:init t) depth) (decode-step (:body t) (inc depth)))
    (and (= :prim (:op t)) (#{'+ '*} (:name t)) (= 2 (count (:args t))))
    (apply c/prim (:name t) (map #(decode-step % depth) (:args t)))
    :else (reject! :step)))

(defn inspect-lowering [source target]
  (c/assert-wf! target)
  (let [{:keys [step seed prefix] :as decoded} (inspect-source source)
        loop-body (get-in target [:body :body :body :body :inits 0 :body])
        iteration (if (some? prefix) (get-in loop-body [:then :then]) (:then loop-body))
        rhs (get-in iteration [:body :args 1 :args 2])
        decoded-step (decode-step rhs 0)
        backedge (c/let1 (c/prim 'nth (c/local 6) (c/local 1))
                        (c/app (c/local 3) (c/prim 'inc (c/local 2))
                               (c/prim 'assoc (c/local 1) (c/quote* 0) rhs)))
        body (c/if* (c/prim '< (c/local 1) (c/local 5))
                    (if (some? prefix) (c/if* (c/prim '< (c/local 1) (c/quote* prefix)) backedge (c/local 0)) backedge)
                    (c/local 0))
        expected (c/lam 1
                        (c/let1 (c/prim 'count (c/local 0))
                          (c/let1 (c/quote* 0)
                            (c/let1 (c/quote* [seed])
                              (c/letrec [(c/lam 2 body)]
                                (c/app (c/local 0) (c/local 2) (c/local 1)))))))]
    (when-not (same-code? (c/lam 2 step) (c/lam 2 decoded-step)) (reject! :step-endpoint))
    (when-not (same-code? expected target) (reject! :loop-protocol))
    (assoc decoded :source-id (c/code-id source) :target-id (c/code-id target)
           :projection :singleton-scalar :decoded-step decoded-step)))

(defn witness
  "Bind the original callback and independently recognized loop to the generic
   indexed-prefix theorem. The theorem itself is over mathematical Nat steps;
   uniform Long loop safety still needs a reachable-accumulator invariant."
  [source target input-bounds]
  (when-not (= 2 (count input-bounds)) (reject! :step-arity))
  (let [en @driver/proof-state
        decoded (inspect-lowering source target)
        scalar (scalar/certify-body (:step decoded) input-bounds)
        core (:core scalar) [xs count acc h safe] (repeatedly 5 k/fvar!)
        vx (e/fvar xs) vn (e/fvar count) va (e/fvar acc)
        length (e/app* (k/c "List.length" [k/l0]) k/Nat vx)
        step (e/app (k/c "scalarStep") core)
        goal (k/pi* [[xs "xs" (k/List k/Nat)] [count "count" k/Nat] [acc "acc" k/Nat]
                     [h "within" (e/app* (k/c "Nat.le") vn length)]]
                    (k/eq k/Nat (e/app* (k/c "scalarRun") vn core vx (e/lit-nat 0) va)
                          (k/foldl k/Nat k/Nat step va (e/app* (k/c "scalarTake") vx vn))))
        proof (k/lam* [[xs "xs" (k/List k/Nat)]] (e/app* (k/c "scalar-indexed-prefix-fold") vx core))
        capacity (e/lit-nat (biginteger Long/MAX_VALUE))
        safe-type (e/app* (k/c "ScalarRunSafe") capacity core vx vn (e/lit-nat 0) va)
        checked-binders [[xs "xs" (k/List k/Nat)] [count "count" k/Nat] [acc "acc" k/Nat]
                         [h "within" (e/app* (k/c "Nat.le") vn length)] [safe "safe" safe-type]]
        checked-goal (k/pi* checked-binders
                           (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                                 (e/app* (k/c "scalarRunChecked") vn core vx (e/lit-nat 0) va capacity)
                                 (e/app* (k/c "Option.some" [k/l0]) k/Nat
                                         (k/foldl k/Nat k/Nat step va (e/app* (k/c "scalarTake") vx vn)))))
        checked-proof (k/lam* checked-binders
                             (e/app* (k/c "scalar-checked-prefix-fold") vx core vn va capacity (e/fvar h) (e/fvar safe)))]
    (when-not (and (env/verifies? en goal proof) (env/verifies? en checked-goal checked-proof)) (reject! :proof))
    (assoc decoded :scalar-witness scalar :goal goal :proof proof
           :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
           :checked-goal checked-goal :checked-proof checked-proof
           :checked-goal-sha256 (k/expr-hash checked-goal) :checked-proof-sha256 (k/expr-hash checked-proof)
           :reachable-safety-premise :required-not-automatically-discharged
           :evidence :kernel-indexed-driver-with-tested-Core-decoder
           :bridges [:loop-decoder :source-reference-host :finite-environment :T0-CEK :reachable-Long-invariant :owned-erasure :JVM])))


(defn verify-witness? [source target input-bounds receipt]
  (try
    (let [expected (witness source target input-bounds) en @driver/proof-state]
      (and (= (select-keys expected [:source-id :target-id :goal :checked-goal :goal-sha256 :checked-goal-sha256])
              (select-keys receipt [:source-id :target-id :goal :checked-goal :goal-sha256 :checked-goal-sha256]))
           (scalar/verify-body-witness? (:step expected) input-bounds (:scalar-witness receipt))
           (= (:proof-sha256 receipt) (k/expr-hash (:proof receipt)))
           (= (:checked-proof-sha256 receipt) (k/expr-hash (:checked-proof receipt)))
           (env/verifies? en (:goal expected) (:proof receipt))
           (env/verifies? en (:checked-goal expected) (:checked-proof receipt))))
    (catch Exception _ false)))


(defn sum-witness
  "Discharge reachable arithmetic safety for the actual +/zero consumer.
   This is a kernel driver theorem plus a tested original-Core loop decoder."
  [source target max-count max-x]
  (when-not (and (instance? Long max-count) (<= 0 max-count)
                 (instance? Long max-x) (<= 0 max-x)
                 (<= (*' max-count max-x) Long/MAX_VALUE)) (reject! :sum-budget))
  (let [en @sum/proof-state decoded (inspect-lowering source target)
        expected (c/prim '+ (c/local 1) (c/local 0))
        _ (when-not (and (zero? (:seed decoded)) (same-code? (:step decoded) expected)) (reject! :sum-step))
        core (scalar/encode-body (:step decoded) 2)
        [xs count within limited elements index] (repeatedly 6 k/fvar!)
        vx (e/fvar xs) vn (e/fvar count) nat #(e/lit-nat (biginteger %))
        upper (nat max-x) cap (nat Long/MAX_VALUE) limit (nat max-count)
        le #(e/app* (k/c "Nat.le") %1 %2)
        length (e/app* (k/c "List.length" [k/l0]) k/Nat vx)
        all-elements (k/pi* [[index "index" k/Nat]] (le (e/app* (k/c "scalarAt") vx (e/fvar index)) upper))
        binders [[xs "xs" (k/List k/Nat)] [count "count" k/Nat]
                 [within "within" (le vn length)] [limited "limited" (le vn limit)]
                 [elements "elements" all-elements]]
        goal (k/pi* binders
                    (k/eq (e/app (k/c "Option" [k/l0]) k/Nat)
                          (e/app* (k/c "scalarRunChecked") vn core vx (nat 0) (nat 0) cap)
                          (e/app* (k/c "Option.some" [k/l0]) k/Nat
                                  (k/foldl k/Nat k/Nat (e/app (k/c "scalarStep") core) (nat 0)
                                           (e/app* (k/c "scalarTake") vx vn)))))
        capacity-proof (e/app* (k/c "Nat.le_of_ble_eq_true") (nat (*' max-count max-x)) cap
                              (e/app* (k/c "Eq.refl" [k/l1]) k/Bool (k/c "Bool.true")))
        budget (e/app* (k/c "Nat.le_trans")
                       (e/app* (k/c "Nat.mul") vn upper)
                       (e/app* (k/c "Nat.mul") limit upper) cap
                       (e/app* (k/c "Nat.mul_le_mul_right") vn limit upper (e/fvar limited)) capacity-proof)
        proof (k/lam* binders (e/app* (k/c "scalar-sum-prefix-total") vx upper cap vn
                                                   (e/fvar elements) (e/fvar within) budget))]
    (when-not (env/verifies? en goal proof) (reject! :sum-proof))
    (assoc decoded :goal goal :proof proof :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
           :max-count max-count :max-x max-x
           :reachable-safety-premise :discharged-for-sum
           :invariant :acc-plus-remaining-times-upper-fits
           :bridges [:source-and-loop-decoder :finite-input-guard :T0-CEK :Long-representation :owned-erasure :JVM])))
