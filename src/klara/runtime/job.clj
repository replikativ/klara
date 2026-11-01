(ns klara.runtime.job
  "Jobs (spec/L3-effects.md#jobs): a computation in a fork of the current
  world, under a budget, whose outcome is data.

  A job is a :job frame on the continuation plus a job record (an atom
  holding the job's world, deferred intents and owned host objects). The
  frame stops effect search (isolation) and owns the budget meter."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.session :as session]
            [klara.runtime.world :as w]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

(def default-steps 1000000)
(def default-intent-limit 10000)

(defn- remaining [^longs meter] (max 0 (aget meter 0)))

(defn- refund!
  "Return unused reserved steps to the parent meter (L3.budget.nesting)."
  [frame]
  (when-let [^longs pm (get-in frame [:parent-dyn :meter])]
    (aset pm 0 (long (+ (aget pm 0) (long (remaining (:meter frame))))))))

(defn- spent [frame] {:steps (- (:reserved frame) (remaining (:meter frame)))})

(defn- outcome [frame status extra]
  (let [j @(:job frame)]
    (merge {:status status :world (:world j) :intents (:intents j) :spent (spent frame)
            ::job (:job frame)}
           extra)))

(defn- leave
  "Pop back into the parent context with `x` as the job's value."
  [st frame x]
  (refund! frame)
  (assoc st :mode :ret :ctl x :env nil :world (:world frame) :mint (:mint frame) :dyn (:parent-dyn frame)))

(defn- error-data [^Throwable ex]
  (merge {:message (.getMessage ex) :class (.getName (class ex))}
         (select-keys (ex-data ex) [:rule :hint])))

(defn- on-return [st frame x] (leave st frame (outcome frame :done {:value x})))

(defn- on-throw [st frame ex]
  (leave st frame (outcome frame :failed {:error (error-data ex) :exception ex})))

(defn- on-exhausted
  "Suspend at the current state: the frames above the job frame and the
   current control are the continuation (L3.budget.exhausted)."
  [st]
  (let [k (:k st)
        i (count (take-while #(not= :job (:f %)) k))
        frame (nth k i)
        suspension {:mode (:mode st) :ctl (:ctl st) :env (:env st)
                    :frames (vec (take i k)) :world (:world st) :mint (:mint st)}]
    (leave (assoc st :k (nthrest k (inc i))) frame
           (outcome frame :exhausted {:continuation suspension}))))

(defn- job-defaults []
  {:io/print (fn [st [s]]
               (let [job (get-in st [:dyn :job])
                     j (swap! job update :intents conj [:io/print s])]
                 (when (> (count (:intents j)) (:intent-limit j))
                   (fail :L3.job.intent-limit (str "job produced more than " (:intent-limit j) " intents")))
                 (assoc st :mode :ret :ctl nil :env nil)))
   :world/define (fn [st [q info]]                                    ; L3.job.define
                   (let [nw (w/put-definition (:world st) q (w/definition q info))]
                     (swap! (get-in st [:dyn :job]) assoc :world nw)
                     (assoc st :mode :ret :ctl q :env nil :world nw)))
   :world/update (fn [st [f]]
                   (let [nw (f (:world st))]
                     (swap! (get-in st [:dyn :job]) assoc :world nw)
                     (assoc st :mode :ret :ctl nil :env nil :world nw)))})

(defn- reserve!
  "Reserve up to `n` steps from the parent meter (L3.budget.nesting)."
  [parent-meter n]
  (if-let [^longs pm parent-meter]
    (let [r (long (min n (max 0 (aget pm 0))))] (aset pm 0 (- (aget pm 0) r)) r)
    n))

(defn- enter
  "Push a job frame and switch to the job's dynamic context."
  [st job steps]
  (let [meter (long-array [(reserve! (get-in st [:dyn :meter]) steps)])
        frame {:f :job :job job :meter meter :reserved (aget meter 0)
               :parent-dyn (:dyn st) :world (:world st) :mint (:mint st)
               :on-return on-return :on-throw on-throw}
        dyn (cond-> {:meter meter :defaults (job-defaults) :session (get-in st [:dyn :session])
                     :job job :on-exhausted on-exhausted}
              ;; L3.job.profile: a job may run without training profiles
              (or (false? (:profile @job)) (get-in st [:dyn :no-profile])) (assoc :no-profile true))]
    (assoc st :k (conj (:k st) frame) :dyn dyn)))

(defn- steps-of [budget] (long (or (:steps budget) default-steps)))

(defn start
  "Enter a new job from `st`: push its frame, fork the world and switch to
   the job's context. The caller then sets the control to run inside it."
  [st opts]
  (let [fork (w/fork (:world st))
        job (atom {:world fork :intents [] :owned #{} :profile (:profile opts)
                   :intent-limit (or (:intent-limit opts) default-intent-limit)})]
    (assoc (enter st job (steps-of (:budget opts))) :world fork :mint nil)))

(b/register! 'klara.job/run                                          ; L3.job.run
  {:kind :intrinsic
   :fn (fn [st [opts thunk]]
         (assoc (start st opts) :mode :apply :ctl [thunk []]))})

(b/register! 'klara.job/run-all                                      ; L3.job.parallel
  {:kind :intrinsic
   :fn (fn [st [opts thunks]]
         ;; Jobs are isolated (a forked world, their own budget, no mutation of
         ;; outside objects), so they may run at the same time. Each runs its
         ;; own machine on its own thread; the parent reserves all budgets
         ;; first and takes back what is left after all have finished.
         (let [thunks (vec thunks)
               n (count thunks)
               steps (steps-of (:budget opts))
               granted (reserve! (get-in st [:dyn :meter]) (* n steps))
               each (quot granted (max n 1))
               run1 (fn [thunk]
                      (let [own (long-array [each])
                            base (assoc st :k () :dyn (assoc (:dyn st) :meter own))
                            s (assoc (start base (assoc opts :budget {:steps each})) :mode :apply :ctl [thunk []])]
                        [(:ctl (m/run-state s)) (aget own 0)]))
               results (mapv deref (mapv #(future (run1 %)) thunks))]
           (when-let [^longs pm (get-in st [:dyn :meter])]
             (aset pm 0 (long (+ (aget pm 0) (+ (- granted (* n each)) (reduce + (map second results)))))))
           (assoc st :mode :ret :ctl (mapv first results) :env nil)))})

(b/register! 'klara.job/resume                                       ; L3.job.resume
  {:kind :intrinsic
   :fn (fn [st [outcome budget]]
         (when-not (= :exhausted (:status outcome))
           (fail :L3.job.resume (str "only an exhausted job can be resumed, not " (:status outcome))))
         (let [{:keys [mode ctl env frames world mint]} (:continuation outcome)
               st (enter st (::job outcome) (steps-of budget))]
           (assoc st :mode mode :ctl ctl :env env :world world :mint mint
                  :k (reduce conj (:k st) (rseq frames)))))})

(b/register! 'klara.job/adopt!                                       ; L3.job.adopt
  {:kind :intrinsic
   :fn (fn [st [outcome]]
         (let [job (::job outcome)]
           (when-not job (fail :L3.job.adopt "not a job outcome"))
           (when (:adopted @job) (fail :L3.job.adopted "this job outcome was already adopted"))
           (when-not (= :done (:status outcome))
             (fail :L3.job.adopt (str "only a finished job can be adopted, not " (:status outcome))))
           (swap! job assoc :adopted true)
           (let [changed (:world outcome)
                 published (if (get-in st [:dyn :job])
                             (let [nw (w/apply-delta changed (:world st))]
                               (when-not nw (fail :L1.session.conflict "conflicting changes in the parent job"))
                               (swap! (get-in st [:dyn :job]) assoc :world nw) nw)
                             (session/publish! (get-in st [:dyn :session]) changed))
                 intents (map (fn [[op & args]]
                                (t/app (t/host 'klara.effect/perform) (map t/const (cons op args))))
                              (:intents outcome))]
             (assoc st :mode :eval :env [] :world published
                    :ctl (m/prepare-term (t/do* (concat intents [(t/const (:value outcome))])))))))})

(b/register! 'klara.job/fork
             {:kind :macro
              :fn (fn [[_ opts & body] _]
                    (list 'klara.job/run opts (list* 'fn* [] body)))})
