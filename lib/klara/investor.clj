(ns klara.investor
  "Deciding what to compile, with which specializer, and whether it pays
  (design/05-specialization.md, design/06-speculation.md#7-the-investor).

  For a function definition the investor
  1. measures what an interpreted call costs, on a recent argument from the
     profile;
  2. explores its alternatives (specializers), each prepared and measured on
     the same argument in its own job, all at the same time;
  3. installs the alternative with the best net gain, expecting as many
     calls again as there were so far, when the gain covers what preparing
     it cost; otherwise it declines;
  4. accounts for everything it spent, chosen or not.

  Running a function on a real argument to measure it is safe because the
  measurement is a job: it sees a fork of the world, cannot mutate anything
  outside, and a measurement that would perform an effect just fails. The
  decision is data."
  (:require [klara.jit :as jit]
            [klara.own :as own]
            [klara.compiler :as compiler]
            [klara.job :as job]
            [klara.world :as world]))

(def alternatives
  "The specializers the investor tries, by name: a function, or
   {:specializer f :opts preparation-options} when the candidate needs more
   than the definitional checker (a certificate). A definition's own
   specializer (^{:klara/specialize f}) is tried as :attached."
  {:as-is (fn [ctx default] (:reference ctx))
   :default (fn [ctx default] (jit/default ctx))
   :in-place {:specializer own/in-place :opts {:certificate {:kind :in-place}}}})

(def min-work
  "Below this much work (jit/work) the investor does not look at a definition."
  1000)

(def budget
  "Steps for preparing an alternative."
  {:steps 50000000})

(def measure-budget
  "Steps for measuring: compiled loops count one step per iteration."
  {:steps 100000000000})

(defn- now [] (System/nanoTime))

(defn per-call
  "Nanoseconds per call of f on args, at steady state: batches of doubling
   size until a batch takes at least 10 ms and agrees with the previous one
   within 10%, after at least 300 ms in all. The first batches are the
   host's warm-up: fresh code (a new candidate) runs slowly until the JVM
   has compiled it, and two cold batches can agree; measuring then would
   favour old code. A single call that takes a second is its own estimate."
  [f args]
  (let [start (now)]
    (loop [n 1 previous nil]
      (let [t0 (now)]
        (dotimes [_ n] (apply f args))
        (let [t1 (now)
              d (- t1 t0)
              per (quot d n)]
          (if (or (>= n 4000000)
                  (>= d 1000000000)
                  (and previous (>= d 10000000) (>= (- t1 start) 300000000)
                       (<= (abs (- per previous)) (quot previous 10))))
            per
            (recur (* 2 n) (when (>= d 1000000) per))))))))

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
  (let [o (job/run {:budget measure-budget :profile false} (fn [] (per-call f args)))]
    (when (= :done (:status o)) {:ns (:value o) :steps (get-in o [:spent :steps])})))

(defn consider
  "Decide about the definition named q. Returns the decision; installs the
   chosen candidate."
  [q]
  (let [ctx (jit/context q)
        ;; calls from outside: a recursive function's own calls run compiled
        ;; inside the measured call, so they are not further calls
        calls (get-in ctx [:profile :entries :external])
        args (get-in ctx [:profile :entries :sample])
        f (world/get (world/current) q)]
    (if (or (nil? calls) (< (jit/work ctx) min-work) (nil? args))
      {:name q :decision :not-hot :calls calls :work (jit/work ctx)}
      (let [alts (cond-> alternatives
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
                              m (assoc :ns-per-call (:ns m))
                              (and (= :ready (:status a)) (nil? m)) (assoc :status :unmeasured))))
                        names prepared)
            ;; expect as many calls again as so far; a saving within the
            ;; measurement's resolution (10%, see per-call) is no saving
            net (fn [a] (let [saving (- (:ns reference) (:ns-per-call a))]
                          (- (if (> (* 10 saving) (:ns reference)) (* calls saving) 0)
                             (:prepare-ns a))))
            ready (filter #(and (= :ready (:status %)) (:ns-per-call %)) tried)
            best (when (and reference (seq ready)) (apply max-key net ready))
            decision {:name q
                      :calls calls
                      :interpreted-ns (:ns reference)
                      :alternatives (mapv #(cond-> (dissoc % :outcome) (:ns-per-call %) (assoc :net-ns (net %))) tried)
                      :spent {:steps (+ (reduce + (map #(or (:spent %) 0) tried)) (or (:steps reference) 0))
                              :prepare-ns (reduce + (map #(or (:prepare-ns %) 0) tried))}}]
        (cond
          (nil? reference) (assoc decision :decision :unmeasurable)
          (and best (pos? (net best)))
          (let [d (assoc decision :decision :compiled :chosen (:name best)
                         :compiled-ns (:ns-per-call best) :expected-gain-ns (net best))]
            ;; the decision is part of the compiled code's provenance
            (compiler/install! (assoc-in (:outcome best) [:provenance :decision] d))
            d)
          :else (assoc decision :decision :declined))))))

(defn interpreted? [x] (= :interpreted (:kind (compiler/explain x))))

(defn invest!
  "Consider every interpreted function definition in namespace ns-sym;
   returns the decisions. What was declined is considered once more after
   the first round: a caller measured while its callees were interpreted
   pays for entering the interpreter on every call."
  [ns-sym]
  (let [round (fn [names] (mapv consider (filter #(interpreted? (world/get (world/current) %)) names)))
        first-round (round (world/names (world/current) ns-sym))
        again (round (map :name (filter #(= :declined (:decision %)) first-round)))
        by-name (into {} (map (juxt :name identity)) (concat first-round again))]
    (mapv #(get by-name (:name %)) first-round)))
