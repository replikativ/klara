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

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

(def default-steps 1000000)
(def default-intent-limit 10000)

(defn- remaining [^longs meter] (max 0 (aget meter 0)))

(defn- refund!
  "Return unused reserved steps to the parent meter (L3.budget.nesting)."
  [frame]
  (when-let [^longs pm (get-in frame [:parent-dyn :meter])]
    (aset pm 0 (+ (aget pm 0) (remaining (:meter frame))))))

(defn- spent [frame] {:steps (- (:reserved frame) (remaining (:meter frame)))})

(defn- outcome [frame status extra]
  (let [j @(:job frame)]
    (merge {:status status :world (:world j) :intents (:intents j) :spent (spent frame)
            ::job (:job frame) ::base (:base j)}
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
    (let [r (min n (max 0 (aget pm 0)))] (aset pm 0 (- (aget pm 0) r)) r)
    n))

(defn- enter
  "Push a job frame and switch to the job's dynamic context."
  [st job steps]
  (let [meter (long-array [(reserve! (get-in st [:dyn :meter]) steps)])
        frame {:f :job :job job :meter meter :reserved (aget meter 0)
               :parent-dyn (:dyn st) :world (:world st) :mint (:mint st)
               :on-return on-return :on-throw on-throw}
        dyn {:meter meter :defaults (job-defaults) :session (get-in st [:dyn :session])
             :job job :on-exhausted on-exhausted}]
    (assoc st :k (conj (:k st) frame) :dyn dyn)))

(defn- steps-of [budget] (long (or (:steps budget) default-steps)))

(b/register! 'klara.job/run                                          ; L3.job.run
  {:kind :intrinsic
   :fn (fn [st [opts thunk]]
         (let [fork (w/fork (:world st))
               job (atom {:world fork :base (:world st) :intents [] :owned #{}
                          :intent-limit (or (:intent-limit opts) default-intent-limit)})]
           (-> (enter st job (steps-of (:budget opts)))
               (assoc :mode :apply :ctl [thunk []] :world fork :mint nil))))})

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
           (let [base (::base outcome) changed (:world outcome)
                 published (if-let [s (get-in st [:dyn :session])]
                             (if (get-in st [:dyn :job])
                               (let [nw (w/merge-into base changed (:world st))]
                                 (when-not nw (fail :L1.session.conflict "conflicting changes in parent job"))
                                 (swap! (get-in st [:dyn :job]) assoc :world nw) nw)
                               (session/publish! s base changed))
                             changed)
                 intents (map (fn [[op & args]]
                                (t/app (t/host 'klara.effect/perform) (map t/const (cons op args))))
                              (:intents outcome))]
             (assoc st :mode :eval :env {} :world published
                    :ctl (t/do* (concat intents [(t/const (:value outcome))]))))))})

(b/register! 'klara.job/fork
             {:kind :macro
              :fn (fn [[_ opts & body] _]
                    (list 'klara.job/run opts (list* 'fn* [] body)))})
