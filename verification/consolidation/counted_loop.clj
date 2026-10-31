(ns consolidation.counted-loop
  "Bounded pure counted loops: exact Core recognition, checked step composition,
   generic/primitive JVM experiments and immutable backedge snapshots."
  (:require [consolidation.scalar-block :as block] [consolidation.scalar-core :as scalar]
            [consolidation.counted-loop-model :as model]
            [ansatz.kernel.expr :as e] [ansatz.kernel.env :as env]
            [klara.fusion.kernel :as k] [klara.core :as c]
            [klara.world :as w] [klara.eval :as ev]))

(defn- reject! [reason] (throw (ex-info "Counted loop declined" {:reason reason})))
(def index-body (c/prim '+ (c/local 1) (c/quote* 1)))

(defn source
  "Construct the admitted one-input loop: i=0, s=seed, while i<n; recur i+1,rhs.
   rhs sees s at local 0 and i at local 1. Captured inputs are not admitted."
  ([rhs] (source rhs 0))
  ([rhs seed]
   (c/lam 1
     (c/let1 (c/quote* 0)
       (c/let1 (c/quote* seed)
         (c/letrec [(c/lam 2 (c/if* (c/prim '< (c/local 1) (c/local 5))
                                      (c/app (c/local 2) index-body rhs) (c/local 0)))]
                   (c/app (c/local 0) (c/local 2) (c/local 1))))))))

(defn inspect [term]
  (c/assert-wf! term)
  (let [seed (get-in term [:body :body :init :datum])
        loop-body (get-in term [:body :body :body :inits 0 :body])
        rhs (get-in loop-body [:then :args 1])]
    (when-not (and (instance? Long seed) (<= 0 seed)
                   (= (c/code-id term) (c/code-id (source rhs seed))))
      (reject! :loop-protocol))
    (scalar/encode-body rhs 2)
    {:seed seed :rhs rhs :loop-body loop-body}))

(defn- app [name & args] (apply e/app* (k/c name) args))
(def state-type (k/c "LoopState"))
(def result-type (e/app (k/c "Option" [k/l0]) state-type))

(defn- run-goal [rhs index-block acc-block]
  (let [[cap count state] (repeatedly 3 k/fvar!) vc (e/fvar cap) vn (e/fvar count) vs (e/fvar state)
        src (app "loopSourceStep" (scalar/encode-body index-body 2) (scalar/encode-body rhs 2) vc)
        dst (app "loopTargetStep" (block/encode-block index-block) (block/encode-block acc-block) vc)]
    (k/pi* [[cap "cap" k/Nat] [count "count" k/Nat] [state "state" state-type]]
           (k/eq result-type (app "loopRun" vn dst vs) (app "loopRun" vn src vs)))))

(defn certify [term]
  (let [{:keys [rhs]} (inspect term)
        index (block/certify index-body 2) acc (block/certify rhs 2)
        en @model/proof-state cap (k/fvar!) vc (e/fvar cap)
        pi (scalar/encode-body index-body 2) pa (scalar/encode-body rhs 2)
        bi (block/encode-block (:block index)) ba (block/encode-block (:block acc))
        src (app "loopSourceStep" pi pa vc) dst (app "loopTargetStep" bi ba vc)
        step (app "loop-step-refines" pi pa bi ba (:proof index) (:proof acc) vc)
        proof (k/lam* [[cap "cap" k/Nat]] (app "loop-runs-refine" src dst step))
        goal (run-goal rhs (:block index) (:block acc))]
    (when-not (env/verifies? en goal proof) (reject! :loop-proof))
    {:source-id (c/code-id term) :index index :acc acc :goal goal :proof proof
     :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}))

(defn verify? [term receipt]
  (try
    (let [{:keys [rhs]} (inspect term)
          goal (run-goal rhs (get-in receipt [:index :block]) (get-in receipt [:acc :block]))]
      (and (= (c/code-id term) (:source-id receipt))
           (block/verify? index-body 2 (:index receipt))
           (block/verify? rhs 2 (:acc receipt))
           (= goal (:goal receipt)) (= (k/expr-hash goal) (:goal-sha256 receipt))
           (= (k/expr-hash (:proof receipt)) (:proof-sha256 receipt))
           (env/verifies? @model/proof-state goal (:proof receipt))))
    (catch Exception _ false)))

(def ^:private anchors {'+ clojure.core/+ '* clojure.core/* '< clojure.core/<})
(defn- check-roots! []
  (doseq [[name f] anchors]
    (when-not (identical? f (get c/prims name)) (reject! :primitive-context))))

(defn- block-expression [receipt primitive?]
  (let [slot #(symbol (str "slot" %))
        bindings (into ['slot0 's 'slot1 'i]
                       (mapcat (fn [[op target a b]]
                                 [(slot target)
                                  (case op
                                    :literal (if primitive? (list 'clojure.core/long a) a)
                                    :copy (slot a)
                                    :add (list (if primitive? 'clojure.core/+ 'add) (slot a) (slot b))
                                    :mul (list (if primitive? 'clojure.core/* 'mul) (slot a) (slot b)))])
                               (get-in receipt [:block :instructions])))]
    (list 'let bindings (slot (get-in receipt [:block :result])))))

(defn- emitted-form [receipt primitive?]
  (let [cast #(if primitive? (list 'clojure.core/long %) %)
        next-index (block-expression (:index receipt) primitive?)
        next-acc (block-expression (:acc receipt) primitive?)]
    (list 'fn ['add 'mul 'less]
      (list 'fn ['n 'initial-i 'initial-s 'fuel]
        (list 'let ['limit '(long n)
                    'initial '(long initial-i)
                    'end-index '(+ initial (min (long fuel) (- limit initial)))
                    'stop (if primitive? 'end-index '(identity end-index))]
          (list 'loop ['i (cast 'initial-i) 's (cast 'initial-s)]
            (list 'if (list (if primitive? 'clojure.core/< 'less) 'i 'stop)
              (list 'let ['next-index next-index 'next-acc next-acc]
                '(recur next-index next-acc))
              ['(if (= i limit) :done :paused) 'i 's])))))))

(defn prepare-certified
  "Admit an existing receipt before hosted emission; useful for measuring the
   proof phase separately. No emitted code is trusted merely for having a receipt."
  [term basis receipt]
   (check-roots!)
   (when-not (verify? term receipt) (reject! :loop-proof))
   (let [decoded (inspect term)
         forms (into {} (for [tier [:generic :primitive]]
                          [tier (emitted-form receipt (= tier :primitive))]))
         bodies (binding [*ns* (the-ns 'consolidation.counted-loop) *unchecked-math* false]
                  (into {} (for [[tier form] forms]
                             [tier ((eval form) (anchors '+) (anchors '*) (anchors '<))])))]
     (assoc decoded :source term :source-id (c/code-id term) :basis basis
            :receipt receipt :forms forms :bodies bodies)))

(defn prepare
  ([term] (prepare term w/empty-root))
  ([term basis] (prepare-certified term basis (certify term))))

(defn- nonnegative-long? [x] (and (instance? Long x) (<= 0 x)))
(defn start [artifact n]
  (check-roots!)
  (when-not (nonnegative-long? n) (reject! :input-layout))
  {:source-id (:source-id artifact) :basis (:basis artifact) :n n :index 0 :acc (:seed artifact)})

(defn- check-state! [artifact {:keys [source-id basis n index acc] :as snapshot}]
  (when-not (and (= #{:source-id :basis :n :index :acc} (set (keys snapshot)))
                 (= source-id (:source-id artifact)) (identical? basis (:basis artifact))
                 (every? nonnegative-long? [n index acc]) (<= index n))
    (reject! :backedge-state)))

(defn run-chunk
  "Pure immutable snapshots, no live mutable lease. Fuel counts complete loop
   iterations, not CEK transitions. No cancellation/suspension inside an RHS."
  [artifact snapshot fuel tier]
  (check-roots!) (check-state! artifact snapshot)
  (when-not (nonnegative-long? fuel) (reject! :fuel))
  (let [f (or (get-in artifact [:bodies tier]) (reject! :tier))
        [status i s] (f (:n snapshot) (:index snapshot) (:acc snapshot) fuel)]
    {:status status :snapshot (assoc snapshot :index i :acc s)}))

(defn invoke [artifact n tier]
  (:acc (:snapshot (run-chunk artifact (start artifact n) Long/MAX_VALUE tier))))

(defn reference-state
  "Rebuild a logical loop-condition state, retaining the original capture
   prefix and pinned world. API-produced snapshots are reachable; arbitrary
   hosted map construction is not an authenticated reachability witness."
  [artifact snapshot]
  (check-roots!) (check-state! artifact snapshot)
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
    (let [basis (:basis artifact) f (ev/run (:source artifact) {:basis basis})
          initial (ev/call-value* f [(:n snapshot)] {:locals [] :basis basis :mint basis} '())]
      (loop [state initial fuel 100]
        (when (zero? fuel) (reject! :reference-entry))
        (let [[mode control environment k] state]
          (if (and (= mode :eval) (= control (:loop-body artifact)))
            (let [locals (:locals environment) count (count locals)]
              [mode control (assoc environment :locals (assoc locals (- count 2) (:index snapshot)
                                                                  (dec count) (:acc snapshot))) k])
            (recur (ev/step-state state) (dec fuel))))))))

(defn resume-reference [artifact snapshot]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
            ev/*reference-driver* true ev/*basis* (:basis artifact) ev/*mint* (:basis artifact)
            ev/*fiber* nil ev/*outer-k* '()]
    (ev/drive (reference-state artifact snapshot))))
