(ns klara.investor
  "Deciding what to compile, with which specializer, and whether it pays
  (design/05-specialization.md, design/06-speculation.md#7-the-investor).

  It works in two tiers, each entered when the time a definition has spent
  interpreted (its profile's events times the interpreter's measured cost
  per event) covers what the tier costs, as a JIT tiers ('ski rental'):
  - baseline: compile the definition as it is, without measuring it, so any
    definition qualifies (impure ones too);
  - explored: for pure definitions with a plain-data sample argument,
    compare the alternatives as below.

  Exploring a function definition, the investor
  1. measures what an interpreted call costs, on a recent argument from the
     profile;
  2. explores its alternatives (specializers), each prepared and measured on
     the same argument in its own job, all at the same time;
  3. installs the alternative with the best expected gain, expecting as many
     calls again as there were so far (what preparing cost is spent by then,
     so it does not count against installing), or declines when none is
     measurably faster than the interpreter;
  4. accounts for everything it spent, chosen or not.

  Running a function on a real argument to measure it is safe because only
  pure definitions (L4.facts.pure) on plain data are measured, in a job: a
  fork of the world that does not train profiles. The decision is data."
  (:require [klara.jit :as jit]
            [klara.time :as time]
            [klara.own :as own]
            [klara.compiler :as compiler]
            [klara.code :as code]
            [klara.stage :refer [lift]]
            [klara.job :as job]
            [klara.world :as world]))

(def alternatives
  "The specializers the investor tries, by name: a function, or
   {:specializer f :opts preparation-options} when the candidate needs more
   than the definitional checker (a certificate). A definition's own
   specializer (^{:klara/specialize f}) is tried as :attached."
  {:as-is (fn [ctx default] (:reference ctx))
   :default (fn [ctx default] (jit/default ctx))
   ;; the default without the world's rules: whether they pay is measured
   :without-rules (fn [ctx default] (jit/default ctx {:rules []}))
   :in-place {:specializer own/in-place :opts {:certificate {:kind :in-place}}}})

(defn data?
  "Plain data: no functions, atoms, arrays or other objects, so a pure
   function called on it can only compute."
  [x]
  (cond (or (nil? x) (number? x) (string? x) (keyword? x) (symbol? x) (boolean? x) (char? x)) true
        (map? x) (every? (fn [[k v]] (and (data? k) (data? v))) x)
        (coll? x) (every? data? x)
        :else false))

(def decisions
  "Every decision so far, by definition name, oldest first. A definition in
   the world like any other: forks have their own, and a decision made inside
   a job is the job's until it is adopted."
  {})

(defn- remember!
  "Record decision d in the world (def is an effect: L1.def.effect)."
  [d]
  (def decisions (update decisions (:name d) (fnil conj []) d))
  d)

(defn interpreted? [x] (= :interpreted (:kind (compiler/explain x))))

(defn- v-fn? "An interpreted function value (a function definition)." [x] (interpreted? x))

(def policy
  "When a definition is worth a tier, in nanoseconds of interpreted time spent
   so far. Compiling as it is costs milliseconds; exploring prepares every
   alternative and measures each for at least 300 ms. `consider` and
   `invest!` take overrides."
  {:baseline-ns 20000000 :explore-ns 500000000})

(defn calibration-loop
  "The loop the interpreter's cost per profile event is measured on."
  [n]
  (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc i)) acc)))

(def calibration
  "Nanoseconds the interpreter spends per profile event, measured once."
  nil)

(defn event-ns
  "The interpreter's cost per profile event: measured on calibration-loop the
   first time and kept (a def, so per world), 100 if it cannot be measured."
  []
  (or calibration
      (let [q 'klara.investor/calibration-loop
            e0 (jit/events (jit/context q))
            t0 (time/now)
            _ (calibration-loop 20000)
            t (- (time/now) t0)
            e (- (jit/events (jit/context q)) e0)
            c (if (and (pos? e) (interpreted? calibration-loop)) (max 1 (quot t e)) 100)]
        (def calibration c)
        c)))

(defn spent-ns
  "Estimated interpreted time the definition has cost so far."
  [ctx]
  (* (jit/events ctx) (event-ns)))

(defn estimated-ns
  "What definition q has cost, as if it had stayed interpreted: its profile's
   estimate, or, once compiled at the baseline (where it no longer
   profiles), what it had cost then scaled by the entries its compiled code
   counted since (L4.jit.trigger)."
  [q ctx]
  (let [base (spent-ns ctx)
        d (peek (get decisions q))
        counted (some-> (compiler/compiled q) compiler/explain :entries)]
    (if (and counted (= :baseline (:tier d)) (pos? (or (:entries-at-compile d) 0)))
      (max base (+ (:spent-ns d) (quot (* (:spent-ns d) counted) (:entries-at-compile d))))
      base)))

(def budget
  "Steps for preparing an alternative."
  {:steps 50000000})

(def measure-budget
  "Steps for measuring: compiled loops count one step per iteration."
  {:steps 100000000000})

(defn- now [] (time/now))

(defn per-call
  "Nanoseconds per call of f on args, at steady state: batches of doubling
   size until a batch takes at least 10 ms and agrees with the previous one
   within 10%, after at least 300 ms in all, with the host's JIT compiler
   idle during both batches. Fresh code (a new candidate) runs slowly, and
   steadily so, until the JVM has compiled it, which under load can take a
   second; measuring then would favour old code. A single call that takes a
   second is its own estimate, and two seconds in all end the measurement."
  [f args]
  (let [start (now)]
    (loop [n 1 previous nil quiet? false]
      (let [c0 (time/compiling)
            t0 (now)]
        (jit/repeat-call n f args)
        (let [t1 (now)
              idle (= c0 (time/compiling))
              d (- t1 t0)
              per (quot d n)]
          (if (or (>= n 4000000)
                  (>= d 1000000000)
                  (>= (- t1 start) 2000000000)
                  (and previous idle quiet? (>= d 10000000) (>= (- t1 start) 300000000)
                       (<= (abs (- per previous)) (quot previous 10))))
            per
            (recur (* 2 n) (when (>= d 1000000) per) idle)))))))

(defn- explore
  "Prepare q with specializer s (called name). Runs inside a job."
  [q name s]
  (let [t0 (now)
        outcome (jit/prepare q (if (map? s)
                                 (merge (:opts s) {:specializer (:specializer s) :specializer-name name})
                                 {:specializer s :specializer-name name}))
        prep (- (now) t0)]
    (if (= :ready (:status outcome))
      {:status :ready :outcome outcome :prepare-ns prep}
      {:status (:status outcome) :why (:message outcome) :prepare-ns prep})))

(defn- measure
  "Nanoseconds per call of f on args, in a job of its own: a measurement
   that would perform an effect or mutate anything outside fails instead."
  [f args]
  (let [t0 (now)
        o (job/run {:budget measure-budget :profile false} (fn [] (per-call f args)))]
    (when (= :done (:status o))
      {:ns (:value o) :steps (get-in o [:spent :steps]) :measure-ns (- (now) t0)})))

(defn- baseline
  "Compile q as it is, unmeasured: compiled code is never slower than the
   interpreter by much, and nothing runs to find out."
  [q d why]
  (let [o (jit/prepare q {:specializer (:as-is alternatives) :specializer-name :as-is :count-entries true})
        d (assoc d :tier :baseline :why why
                 :entries-at-compile (get-in (jit/context q) [:profile :entries :count]))]
    (if (= :ready (:status o))
      (let [d (assoc d :decision :compiled :chosen :as-is)]
        (compiler/install! (assoc-in o [:provenance :decision] d))
        d)
      (assoc d :decision :declined :rejected (:message o)))))

(defn- decide
  [q pol]
  (let [ctx (jit/context q)
        spent (estimated-ns q ctx)
        ;; calls from outside: a recursive function's own calls run compiled
        ;; inside the measured call, so they are not further calls
        calls (get-in ctx [:profile :entries :external])
        args (get-in ctx [:profile :entries :sample])
        ;; the definition's own function, as the alternatives run: not pinned
        f (:function ctx)]
    (cond
      (or (nil? calls) (< spent (:baseline-ns pol)))
      {:name q :decision :not-hot :calls calls :spent-ns spent}
      (< spent (:explore-ns pol))
      (baseline q {:name q :calls calls :spent-ns spent} "not yet worth exploring")
      ;; measuring runs the definition: only where that changes nothing but time
      (not (:pure (jit/pure? q)))
      (baseline q {:name q :calls calls :spent-ns spent} (str "unmeasurable: " (:why (jit/pure? q))))
      ;; samples that are not plain data are held weakly (L4.profile.record)
      (nil? args)
      (baseline q {:name q :calls calls :spent-ns spent} "unmeasurable: no sample arguments are kept")
      (not (data? args))
      (baseline q {:name q :calls calls :spent-ns spent} "unmeasurable: its sample arguments are not plain data")
      :else
      (let [alts (cond-> alternatives
                   (empty? jit/rules) (dissoc :without-rules)
                   (:specializer ctx) (assoc :attached (:specializer ctx)))
            names (vec (keys alts))
            ;; explore in parallel: preparing is checking, independent per alternative
            prepared (job/run-all {:budget budget} (map (fn [k] (fn [] (explore q k (get alts k)))) names))
            ;; measure one at a time: timing must not compete with itself
            reference (measure f args)
            tried (mapv (fn [k o]
                          (let [a (if (= :done (:status o)) (:value o) {:status :failed :why (get-in o [:error :message])})
                                m (when (= :ready (:status a)) (measure (compiler/executable (:outcome a)) args))]
                            (cond-> (assoc a :name k :spent (get-in o [:spent :steps]))
                              m (assoc :ns-per-call (:ns m) :measure-ns (:measure-ns m))
                              (and (= :ready (:status a)) (nil? m)) (assoc :status :unmeasured))))
                        names prepared)
            ;; expect as many calls again as so far; a saving within the
            ;; measurement's resolution (10%, see per-call) is no saving.
            ;; What preparing cost is spent now, whatever is chosen: it decided
            ;; whether to explore (L4.jit.tiers), not what to install
            net (fn [a] (let [saving (- (:ns reference) (:ns-per-call a))]
                          (if (> (* 10 saving) (:ns reference)) (* calls saving) 0)))
            ready (filter #(and (= :ready (:status %)) (:ns-per-call %)) tried)
            fastest (when (and reference (seq ready)) (apply max-key net ready))
            ;; within the resolution of as-is, as-is: no guards, and no
            ;; premises on callees (an inlined callee's redefinition retires it)
            as-is (first (filter #(= :as-is (:name %)) ready))
            best (if (and as-is fastest
                          (<= (* 10 (- (:ns-per-call as-is) (:ns-per-call fastest))) (:ns-per-call as-is)))
                   as-is
                   fastest)
            decision {:name q
                      :tier :explored
                      :calls calls
                      :spent-ns spent
                      :interpreted-ns (:ns reference)
                      :alternatives (mapv #(cond-> (dissoc % :outcome) (:ns-per-call %) (assoc :net-ns (net %))) tried)
                      :spent {:steps (+ (reduce + (map #(or (:spent %) 0) tried)) (or (:steps reference) 0))
                              :prepare-ns (reduce + (map #(or (:prepare-ns %) 0) tried))
                              ;; measuring is spent too (usually more than preparing)
                              :measure-ns (+ (or (:measure-ns reference) 0)
                                             (reduce + (map #(or (:measure-ns %) 0) tried)))}}]
        (cond
          (nil? reference) (assoc decision :decision :unmeasurable)
          (and best (pos? (net best)))
          (let [d (assoc decision :decision :compiled :chosen (:name best)
                         :compiled-ns (:ns-per-call best) :expected-gain-ns (net best))]
            ;; the decision is part of the compiled code's provenance
            (compiler/install! (assoc-in (:outcome best) [:provenance :decision] d))
            d)
          ;; nothing measurably faster: still past the baseline, so compiled as it
          ;; is (a callee left interpreted costs its compiled callers an entry
          ;; into the interpreter on every call, which measuring alone cannot see)
          (compiler/compiled q) (assoc decision :decision :kept :why "explored: none measurably faster than its compiled code")
          :else (baseline q decision "explored: none measurably faster"))))))

(defn- globals
  "The names of the globals that Code c refers to."
  [c]
  (let [v (code/view c)]
    (if (= :global (:op v)) [(:name v)] (mapcat globals (code/children c)))))

(defn- visit [deps [seen out] q]
  (if (contains? seen q)
    [seen out]
    (let [[seen out] (reduce (fn [acc d] (visit deps acc d)) [(conj seen q) out] (get deps q))]
      [seen (conj out q)])))

(defn- calls-among
  "For each of the function definitions `names`, the ones among them it calls."
  [names]
  (let [in (set names)]
    (into {} (map (fn [q] [q (filter in (distinct (some-> (code/unfold (lift (world/get (world/current) q))) globals)))]))
          names)))

(defn callees-first
  "Function definitions `names` ordered so that each comes after the ones it
   calls (within a cycle, in any order): a caller is then measured with its
   callees compiled, not entering the interpreter on every call."
  [names]
  (second (reduce (fn [acc q] (visit (calls-among names) acc q)) [#{} []] names)))

(defn- reaches? [deps from to]
  (loop [todo (vec (get deps from)) seen #{}]
    (cond (empty? todo) false
          (= to (peek todo)) true
          (contains? seen (peek todo)) (recur (pop todo) seen)
          :else (recur (into (pop todo) (get deps (peek todo))) (conj seen (peek todo))))))

(defn in-cycles
  "The definitions among `names` that call themselves through others (or
   directly): no order puts all their callees first."
  [names]
  (let [deps (calls-among names)]
    (set (filter #(reaches? deps % %) names))))

(defn consider
  "Decide about the definition named q. Returns the decision, also recorded
   in `decisions`; installs the chosen candidate. `pol` overrides `policy`."
  ([q] (consider q {}))
  ([q pol] (remember! (decide q (merge policy pol)))))

(defn invest!
  "Consider every interpreted function definition in namespace ns-sym;
   returns the decisions. What was declined is considered once more after
   the first round: a caller measured while its callees were interpreted
   pays for entering the interpreter on every call."
  ([ns-sym] (invest! ns-sym {}))
  ([ns-sym pol]
  (let [fns (filter #(v-fn? (world/get (world/current) %)) (world/names (world/current) ns-sym))
        cyclic (in-cycles fns)
        ;; within a cycle, all compiled as they are first, so that each is
        ;; then measured with the others compiled
        _ (doseq [q (callees-first (filter cyclic fns))]
            (when (nil? (compiler/compiled q)) (consider q (assoc (merge policy pol) :explore-ns Long/MAX_VALUE))))
        round (fn [names] (mapv #(consider % pol)
                                (callees-first
                                 (filter #(or (nil? (compiler/compiled %))
                                              (and (cyclic %) (= :baseline (:tier (peek (get decisions %))))))
                                         names))))
        first-round (round fns)
        again (round (map :name (filter #(= :declined (:decision %)) first-round)))
        by-name (into {} (map (juxt :name identity)) (concat first-round again))]
    (mapv #(get by-name (:name %)) first-round))))

(defn tick!
  "Consider the interpreted function definitions of namespaces `nss` that
   have spent past the baseline (L4.jit.tiers), each again only once its
   interpreted time has doubled since its last decision (L4.jit.trigger).
   Returns the decisions made."
  ([nss] (tick! nss {}))
  ([nss pol]
   (let [pol (merge policy pol)
         w (world/current)]
     (vec (for [ns nss
                q (callees-first (filter #(v-fn? (world/get w %)) (world/names w ns)))
                :let [last-d (peek (get decisions q))]
                ;; interpreted, or compiled at the baseline and so still promotable
                :when (and (v-fn? (world/get w q))
                           (or (nil? (compiler/compiled q)) (= :baseline (:tier last-d))))
                :let [s (estimated-ns q (jit/context q))
                      last-s (:spent-ns last-d)]
                :when (and (>= s (:baseline-ns pol))
                           (or (nil? last-s) (>= s (* 2 last-s)))
                           ;; a baseline definition is considered again to explore it
                           (or (not= :baseline (:tier last-d)) (>= s (:explore-ns pol))))]
            (consider q pol))))))
