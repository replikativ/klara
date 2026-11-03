(ns klara.runtime.job
  "Jobs (spec/L3-effects.md#jobs): a computation in a fork of the current
  world, under a budget, whose outcome is data.

  A job is a :job frame on the continuation plus a job record (an atom
  holding the job's world, deferred intents and owned host objects). The
  frame stops effect search (isolation) and owns the budget: the step meter
  and the job's wallet (klara.runtime.account), which settles when the job
  ends, whatever its status (L3.account.settle)."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.account :as acct]
            [klara.runtime.machine :as m]
            [klara.runtime.stack :as ks]
            [klara.runtime.session :as session]
            [klara.runtime.world :as w]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

(def default-steps 1000000)
(def default-intent-limit 10000)

(defn- settle!
  "Settle the job's wallet into its parent's (L3.account.settle,
   L3.budget.nesting) and return its receipt (L3.account.receipt)."
  [frame]
  (acct/settle! (:wallet frame) (get-in frame [:parent-dyn :meter]) (:granted frame)))

(defn- outcome [frame status extra]
  (let [j @(:job frame)
        receipt (settle! frame)]
    (merge {:status status :world (:world j) :intents (:intents j)
            :spent (:spent receipt) :receipt receipt
            ::job (:job frame)}
           extra)))

(defn- leave
  "Pop back into the parent context with `x` (an outcome, so the job has
   settled) as the job's value."
  [st frame x]
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
  (let [[frames frame below] (ks/split-at-job (:k st))
        suspension {:mode (:mode st) :ctl (:ctl st) :env (:env st)
                    :frames frames :world (:world st) :mint (:mint st)}]
    (leave (assoc st :k below) frame
           (outcome frame :exhausted
                    (if (::m/in-host st)
                      ;; inside a host call there is no continuation to keep: the
                      ;; outcome is final (resuming it would run the call again)
                      {:resumable false
                       :message "the budget ran out inside a host call, which cannot be resumed"}
                      ;; an outcome is a handle: resumed at most once (L3.job.resumed)
                      {:continuation suspension ::resumable (atom true)})))))

(defn- job-defaults []
  {:time/now (fn [st _] (assoc st :mode :ret :ctl (System/nanoTime) :env nil))   ; L3.effect.time
   :time/compiling (fn [st _] (assoc st :mode :ret :ctl (session/compiling-ms) :env nil))
   :io/print (fn [st [s]]
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

(defn- enter
  "Push a job frame for `grant` (a vector with the reserved :steps,
   klara.runtime.account/grant!) and switch to the job's dynamic context."
  [st job grant]
  (let [meter (long-array [(long (:steps grant))])
        wallet (acct/child-wallet (get-in st [:dyn :wallet]) meter (dissoc grant :steps))
        frame (ks/job-frame {:job job :meter meter :wallet wallet :granted grant
                             :parent-dyn (:dyn st) :world (:world st) :mint (:mint st)
                             :on-return on-return :on-throw on-throw})
        dyn (cond-> {:meter meter :wallet wallet :defaults (job-defaults) :session (get-in st [:dyn :session])
                     :job job :on-exhausted on-exhausted}
              ;; L3.job.profile: a job may run without training profiles
              (or (false? (:profile @job)) (get-in st [:dyn :no-profile])) (assoc :no-profile true))]
    (assoc st :k (ks/push (:k st) frame) :dyn dyn)))

(defn- grant! [st budget withdrawn]
  (acct/grant! (:dyn st) budget default-steps withdrawn))

(defn start
  "Enter a new job from `st`: reserve its budget from the current wallet
   (L3.account.wallet), push its frame, fork the world and switch to the
   job's context. The caller then sets the control to run inside it."
  [st opts]
  (let [grant (grant! st (:budget opts) (::withdrawn opts))
        fork (w/fork (:world st))
        job (atom {:world fork :intents [] :owned #{} :profile (:profile opts)
                   :intent-limit (or (:intent-limit opts) default-intent-limit)})]
    (assoc (enter st job grant) :world fork :mint nil)))

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
         (when (acct/token? (:budget opts))
           (fail :L3.job.parallel "parallel jobs take a budget vector each; split the token and use job/run"))
         (let [thunks (vec thunks)
               n (count thunks)
               budget (acct/vector! (or (:budget opts) {}))
               steps (long (get budget :steps default-steps))
               ;; the non-step part of every budget is withdrawn at once, so
               ;; either all jobs start or none does (L3.account.insufficient)
               each-rest (dissoc budget :steps)
               _ (when (and (seq each-rest) (pos? n))
                   (acct/withdraw! (or (get-in st [:dyn :wallet]) (fail :L3.account.wallet "there is no wallet in this context"))
                                   (acct/scale each-rest n)))
               granted (let [pm (get-in st [:dyn :meter])]
                         (if pm (let [^longs pm pm r (min (* n steps) (max 0 (aget pm 0)))] (aset pm 0 (- (aget pm 0) r)) r)
                             (* n steps)))
               each (quot granted (max n 1))
               run1 (fn [thunk]
                      (let [own (long-array [each])
                            base (assoc st :k ks/empty-stack :dyn (assoc (:dyn st) :meter own))
                            s (assoc (start base (assoc opts :budget {:steps each} ::withdrawn each-rest))
                                     :mode :apply :ctl [thunk []])]
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
         (when-not (:continuation outcome)
           (fail :L3.job.resume "this job ran out of budget inside a host call and cannot be resumed"))
         ;; resuming twice would run two continuations of one job against its
         ;; one record (intents, world, adoption): an outcome is resumed once
         (when-not (compare-and-set! (::resumable outcome) true false)
           (fail :L3.job.resumed "this outcome was already resumed"))
         (let [{:keys [mode ctl env frames world mint]} (:continuation outcome)
               ;; a new grant and wallet: tokens of the settled one are foreign now
               st (enter st (::job outcome) (grant! st budget nil))]
           (assoc st :mode mode :ctl ctl :env env :world world :mint mint
                  :k (ks/reinstate (:k st) frames))))})

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
