(ns klara.runtime.stack
  "The continuation of the reference machine: K in the CEK machine
  (klara.runtime.machine).

  A continuation is a stack of frames, innermost first. Every frame is plain
  data, so a captured continuation is a vector of frames and resuming it
  pushes them back: handlers are deep and continuations multi-shot
  (L3.handle.deep, L3.cont.multishot). Frames are made and taken apart only
  here and in the machine's steps; everything else (effects, jobs, nested
  machines, compiled code leaving) goes through the operations below.

  The frame kinds, the grammar of K:

    evaluation in progress
      :args           a call: the values so far, the argument nodes to go
      :let            the body of a let whose initializer runs
      :if             the branches of an if whose test runs
      :do             the expressions of a do still to run
      :interop        a host member access: its arguments so far
      :code           a code construction: its holes so far (L2.code.*)
      :throw          a throw whose argument runs
      :def            a def whose initializer runs (L1.world.define)
    context restored on return
      :restore        the world and mint of a call in another basis (L1.context.*)
      :restore-profile the profiling flag (L4.profile.record)
      :binders        names bound by a code constructor in progress (L2.code.binders)
      :frame-fn       a host function given the returned value (intrinsics)
    control
      :try            catch clauses and finally (L0.eval.exception)
      :finally-value  a value returned once the finally clause has run
      :finally-ret    a finally clause to run after a catch arm
      :finally-throw  an exception rethrown once the finally clause has run
    delimiters
      :handle         a handler (L3.handle.deep): the effect search stops at
                      a handle for the operation performed
      :job            a job (L3.job.*): the search stops, and so do
                      exceptions, exhaustion and suspension
      :boundary       the bottom of a nested machine (host callbacks, compiled
                      code): the search stops (L3.effect.host-boundary)")

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------------------
;; Frames

(defn kind
  "The kind of frame `f` (see the namespace doc)."
  [f]
  (:f f))

(defn args-frame [node todo vals env recur] {:f :args :node node :todo todo :vals vals :env env :recur recur})
(defn let-frame [body env] {:f :let :body body :env env})
(defn if-frame [node then else env] {:f :if :node node :then then :else else :env env})
(defn do-frame [rest env] {:f :do :rest rest :env env})
(defn interop-frame [term todo vals env] {:f :interop :term term :todo todo :vals vals :env env})
(defn code-frame [node env hole-env tmpl bound todo vals]
  {:f :code :node node :env env :hole-env hole-env :tmpl tmpl :bound bound :todo todo :vals vals})
(def throw-frame {:f :throw})
(defn def-frame [term] {:f :def :term term})

(defn restore-frame [world mint] {:f :restore :world world :mint mint})
(defn restore-profile-frame [no-profile] {:f :restore-profile :no-profile no-profile})
(defn binders-frame [bound] {:f :binders :bound bound})
(defn fn-frame
  "A frame that hands the returned value to (f state value), which returns
   the next state."
  [f]
  {:f :frame-fn :fn f})

(defn try-frame [catches finally env world mint]
  {:f :try :catches catches :finally finally :env env :world world :mint mint})
(defn finally-value-frame [value] {:f :finally-value :value value})
(defn finally-ret-frame [term env] {:f :finally-ret :term term :env env})
(defn finally-throw-frame [ex] {:f :finally-throw :ex ex})

(defn handle-frame [handlers return world mint]
  {:f :handle :handlers handlers :return return :world world :mint mint})
(defn job-frame
  "A job's frame: {:job :meter :wallet :granted :parent-dyn :world :mint
   :on-return :on-throw} (klara.runtime.job)."
  [fields]
  (assoc fields :f :job))
(defn boundary-frame
  "The bottom frame of a nested machine. `deopt?`: compiled code called it,
   so an effect nobody inside handles leaves with the state (L4.exec.leave).
   `outer-k`: the continuation of the host call, for constructing."
  [deopt? outer-k]
  {:f :boundary :deopt deopt? :outer-k outer-k})

(defn stop?
  "Does frame `f` stop the effect search, exceptions and exhaustion?"
  [f]
  (let [x (kind f)] (or (identical? x :job) (identical? x :boundary))))

;; ---------------------------------------------------------------------------
;; Stacks

(def empty-stack ())

(defn push [k f] (conj k f))

(defn find-handler
  "The position of the nearest frame on `k` that is a handle for `op` or a
   stop frame (:job, :boundary), or -1."
  ^long [k op]
  (loop [k (seq k) i 0]
    (if-let [f (first k)]
      (let [x (kind f)]
        (cond
          (identical? x :handle) (if (contains? (:handlers f) op) i (recur (next k) (inc i)))
          (or (identical? x :job) (identical? x :boundary)) i
          :else (recur (next k) (inc i))))
      -1)))

(defn split!
  "Move the top `n` frames of `k` into array `a`, innermost first, and
   return the stack below them."
  [k ^objects a ^long n]
  (loop [k k j 0]
    (if (< j n) (do (aset a j (first k)) (recur (rest k) (inc j))) k)))

(defn reinstate
  "Push captured frames (a vector, innermost first) back onto `k`."
  [k frames]
  (reduce conj k (rseq frames)))

(defn stop-frame
  "The first stop frame on `k`, or nil."
  [k]
  (some #(when (stop? %) %) k))

(defn split-at-job
  "[frames job-frame below]: the frames above the nearest job frame on `k`
   (a vector, innermost first), the job frame and the stack below it."
  [k]
  (let [i (count (take-while #(not (identical? :job (kind %))) k))]
    [(vec (take i k)) (nth k i) (nthrest k (inc i))]))

(defn above-boundary
  "The frames of `k` above its first boundary frame, innermost first."
  [k]
  (take-while #(not (identical? :boundary (kind %))) k))

(defn count-kind
  "The number of frames of kind `x` on `k`."
  [k x]
  (count (filter #(identical? x (kind %)) k)))

(defn constructing
  "Fresh names bound by code constructions still in progress on `k`
   (L2.code.extrusion is checked against the dynamic extent of construction).
   A :binders frame (code/fn*, code/loop*) binds names the same way. A host
   callback is part of that extent: at its boundary the search goes on in
   the continuation of the host call."
  [k]
  (or (some (fn [f]
              (case (kind f)
                (:code :binders) (:bound f)
                :boundary (when-let [ok (:outer-k f)] (constructing ok))
                nil))
            k)
      #{}))

(defn frame-nodes
  "The nodes of frame `f` that locate it in the source, most specific first
   (for Klara stack traces, L0.trace.positions)."
  [f]
  [(:body f) (:then f) (:node f) (first (:todo f)) (:term f)])
