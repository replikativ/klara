(ns consolidation.proved-accumulator
  "Proof-bearing admission for the counted singleton subclass of inferred
   affine code. Helper/loop model proofs are checked; core reification,
   normalization and the native eraser remain explicit implementation bridges."
  (:require [consolidation.helper-bridge :as h]
            [consolidation.source-model :as source-model]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.fusion.kernel :as k]
            [klara.stage :as stage]))

(def version "proof-bearing-singleton-2")

;; Bootstrap model definitions before registering the operational preparation
;; effect. Candidate jobs only read this checked immutable Env; they do not
;; invoke the ansatz DSL or initialize its global REPL session.
(def bootstrap
  (let [start (System/nanoTime) environment @h/proof-state]
    {:environment environment :milliseconds (/ (- (System/nanoTime) start) 1e6)}))

(defn counter-template [seed]
  ;; Exact indexed core produced by the admitted strict loop. The captured n
  ;; is index5 in the loop, i index1 and acc index0. Compare terms, not names.
  (c/lam 1
    (c/let1 (c/quote* 0)
      (c/let1 (c/quote* [seed])
        (c/letrec
          [(c/lam 2
             (c/if* (c/prim '< (c/local 1) (c/local 5))
                    (c/app (c/local 2) (c/prim 'inc (c/local 1))
                           (c/prim 'assoc (c/local 0) (c/quote* 0)
                                   (c/prim 'inc (c/prim 'nth (c/local 0) (c/quote* 0)))))
                    (c/local 0)))]
          (c/app (c/local 0) (c/local 2) (c/local 1)))))))

(defn owned-template [seed callback]
  (c/lam 1
    (c/let1 (c/quote* 0)
      (c/let1 (c/quote* [seed])
        (c/let1 (c/perform nil :own/alloc (c/quote* [seed]))
          (c/let1
            (c/letrec
              [(c/lam 1
                 (c/if* (c/prim '< (c/local 0) (c/local 5))
                        (c/let1 (c/prim 'inc (c/local 0))
                          (c/let1 (c/perform nil :own/update (c/local 3) callback)
                            (c/app (c/local 3) (c/local 1))))
                        (c/quote* nil)))]
              (c/app (c/local 0) (c/local 3)))
            (c/perform nil :own/freeze (c/local 1))))))))

(defn owned-callback [owned seed]
  (let [callback (get-in owned [:body :body :body :body :init :inits 0
                               :body :then :body :init :args 1])]
    (when-not (and callback (= owned (owned-template seed callback)))
      (throw (ex-info "owned endpoint does not implement the proved counted region protocol"
                      {:reason :target-model})))
    callback))

(defn model [base]
  (let [inference (:inference base) seed (get-in inference [:facts 0 :initial])
        term (get-in inference [:analysis :term])
        called (into #{} (comp (filter #(= :summary-call (:rule %))) (map :summary-id))
                     (get-in inference [:analysis :rules]))
        helpers (vals (select-keys (get-in inference [:analysis :summaries]) called))
        original (source-model/extract (:generic base) (:summary-inputs base))]
    (when-not (and (= 1 (count seed)) (instance? Long (first seed)) (<= 0 (first seed))
                   (= term (counter-template (first seed))) (= (:seed original) (first seed)))
      (throw (ex-info "normalized core is outside the counted singleton proof fragment"
                      {:reason :model-shape})))
    {:kind :counted-singleton :seed (first seed) :normalized-id (c/code-id term)
     :original-source-id (:source-id original) :original-step-id (k/expr-hash (:step original))
     :owned-id (c/code-id (:owned inference))
     :callback-id (c/code-id (owned-callback (:owned inference) (first seed)))
     :helper-contracts
     (mapv (fn [summary]
             {:source (:source summary)
              :relation (case (get-in summary [:result :layout])
                          :long-vector :vector-step
                          :long :scalar-step
                          (throw (ex-info "helper result needs another semantic contract"
                                          {:reason :helper-contract})))})
           (sort-by :source-id helpers))}))

(defn receipts [witnesses]
  (mapv (fn [w]
          (cond-> {:role (:role w) :relation (:relation w) :source-id (:source-id w)
                   :goal-sha256 (:goal-sha256 w) :proof-sha256 (:proof-sha256 w)}
            (:private-proof w)
            (assoc :private-goal-sha256 (k/expr-hash (h/private-goal (:term w)))
                   :private-proof-sha256 (k/expr-hash (:private-proof w))))) witnesses))

(stage/register-checker!
 :klara.compile/proved-accumulator
 (fn [exe]
   (try
     (let [base (:base-executable exe) m (model base) contracts (:helper-contracts m)
           original (source-model/extract (:generic base) (:summary-inputs base))
           callback (owned-callback (get-in base [:inference :owned]) (:seed m))
           ws (:kernel-witnesses exe) step (:step-witness exe) target (:target-witness exe)
           rs (receipts (concat [step target] ws))]
       (when-not (and (nil? (stage/check-certificate base))
                      (= version (get-in exe [:certificate :checker-version]))
                      (= :proved-helper-and-private-model (get-in exe [:certificate :kind]))
                      (= (:code-id exe) (:code-id base))
                      (= (:generic exe) (:generic base))
                      (= (:model exe) m)
                      (= (:guards exe) (conj (:guards base) [:arg 0 [:long-range 0 Long/MAX_VALUE]]))
                      (identical? (:run exe) (:run base))
                      (= (count contracts) (count ws))
                      (every? true? (map (fn [{:keys [source relation]} w]
                                          (h/verify-witness? source relation w)) contracts ws))
                      (h/verify-term-witness? (:step original) (:source-id original) step)
                      (h/verify-witness? callback :vector-step target)
                      (= (:witness-receipts exe) rs)
                      (= (:certificate-digest exe)
                         (stage/digest {:model m :witnesses rs :base (:certificate base)}))
                      (= (:certificate-digest exe) (get-in exe [:certificate :bridge-digest])))
         :invalid-proved-accumulator))
     (catch Exception _ :invalid-proved-accumulator))))

(defn prepare [root source]
  (let [start (System/nanoTime) candidate (ia/prepare root source)
        base (.-executable ^klara.compile.staged.Prepared candidate)
        info (staged/prepared-info candidate) m (model base)
        original (source-model/extract (:generic base) (:summary-inputs base))
        step (assoc (h/witness-term (:step original) (:source-id original)) :role :source-step)
        callback (owned-callback (get-in base [:inference :owned]) (:seed m))
        target (assoc (h/witness callback) :role :owned-callback)
        witnesses (mapv (fn [{:keys [source relation]}]
                          (assoc (h/witness source relation) :role :helper)) (:helper-contracts m))
        rs (receipts (concat [step target] witnesses))
        digest (stage/digest {:model m :witnesses rs :base (:certificate base)})
        guards (conj (:guards base) [:arg 0 [:long-range 0 Long/MAX_VALUE]])
        cert (-> (stage/certify (:code-id base) guards :klara.compile/proved-accumulator
                               {:obligation :actual-helper-to-counted-private-model
                                :bridges :tested-core-model-and-native-eraser})
                 (dissoc :digest)
                 (assoc :kind :proved-helper-and-private-model :checker-version version :bridge-digest digest))
        exe {:code-id (:code-id base) :generic (:generic base) :guards guards
             :run (:run base) :base-executable base :model m :kernel-witnesses witnesses
             :step-witness step
             :target-witness target
             :witness-receipts rs :certificate-digest digest
             :certificate (assoc cert :digest (stage/digest cert))}]
    (klara.compile.staged.Prepared.
      source exe (assoc info :evidence :proved-helper-and-private-model
                       :model m :witness-receipts rs :guards guards
                       :base-compile-ms (:compile-ms info)
                       :compile-ms (/ (- (System/nanoTime) start) 1e6)
                       :shared-bootstrap-ms (:milliseconds bootstrap)
                       :implementation-bridges :tested))))

(ev/register-reference-handler!
 :stage/prepare-affine-proved
 (fn [[source] env]
   (try (prepare (:basis env) source)
        (catch clojure.lang.ExceptionInfo ex
          {:status :declined :reason (or (:reason (ex-data ex)) :unsupported-proof)
           :diagnostic (ex-message ex)}))))
