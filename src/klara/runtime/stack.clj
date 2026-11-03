(ns klara.runtime.stack
  "The continuation of the reference machine: K in the CEK machine
  (klara.runtime.machine).

  A continuation is a stack of frames, innermost first. Every frame is plain
  data, so a captured continuation is a vector of frames and resuming it
  pushes them back: handlers are deep and continuations multi-shot
  (L3.handle.deep, L3.cont.multishot). Frames are made and taken apart only
  here and in the machine's steps; everything else (effects, jobs, nested
  machines, compiled code leaving) goes through the operations below.

  The frame kinds, the grammar of K (one record type each, below):

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
;;
;; One record type per kind, with a constant tag for the machine's dispatch
;; (as prepared nodes have, klara.runtime.prepare). Fields are read by name,
;; as keywords on slow paths and as fields in the machine's steps.

(definterface IFrame
  (^long tag [])
  (kind []))

(defmacro ^:private defframe [name tag kind fields]
  `(defrecord ~name ~fields
     IFrame (~'tag [_#] ~tag) (~'kind [_#] ~kind)))

(def ^:const ARGS 0) (def ^:const LET 1) (def ^:const IF 2) (def ^:const DO 3)
(def ^:const INTEROP 4) (def ^:const CODE 5) (def ^:const THROW 6) (def ^:const DEF 7)
(def ^:const RESTORE 8) (def ^:const RESTORE-PROFILE 9) (def ^:const BINDERS 10) (def ^:const FRAME-FN 11)
(def ^:const TRY 12) (def ^:const FINALLY-VALUE 13) (def ^:const FINALLY-RET 14) (def ^:const FINALLY-THROW 15)
(def ^:const HANDLE 16) (def ^:const JOB 17) (def ^:const BOUNDARY 18)

(defframe ArgsFrame 0 :args [node todo vals env recur-arity])
(defframe LetFrame 1 :let [body env])
(defframe IfFrame 2 :if [node then else env])
(defframe DoFrame 3 :do [exprs env])
(defframe InteropFrame 4 :interop [term todo vals env])
(defframe CodeFrame 5 :code [node env hole-env tmpl bound todo vals])
(defframe ThrowFrame 6 :throw [])
(defframe DefFrame 7 :def [term])
(defframe RestoreFrame 8 :restore [world mint])
(defframe RestoreProfileFrame 9 :restore-profile [no-profile])
(defframe BindersFrame 10 :binders [bound])
(defframe FnFrame 11 :frame-fn [callback])
(defframe TryFrame 12 :try [catches finally-node env world mint])
(defframe FinallyValueFrame 13 :finally-value [value])
(defframe FinallyRetFrame 14 :finally-ret [term env])
(defframe FinallyThrowFrame 15 :finally-throw [ex])
(defframe HandleFrame 16 :handle [handlers return world mint])
(defframe JobFrame 17 :job [job meter wallet granted parent-dyn world mint on-return on-throw])
(defframe BoundaryFrame 18 :boundary [deopt outer-k])

(defn tag
  "The tag of frame `f` (the constants above)."
  ^long [f]
  (.tag ^IFrame f))

(defn kind
  "The kind of frame `f` (see the namespace doc), or nil for nil."
  [f]
  (when f (.kind ^IFrame f)))

(defn args-frame [node todo vals env recur-arity] (ArgsFrame. node todo vals env recur-arity))
(defn let-frame [body env] (LetFrame. body env))
(defn if-frame [node then else env] (IfFrame. node then else env))
(defn do-frame [exprs env] (DoFrame. exprs env))
(defn interop-frame [term todo vals env] (InteropFrame. term todo vals env))
(defn code-frame [node env hole-env tmpl bound todo vals] (CodeFrame. node env hole-env tmpl bound todo vals))
(def throw-frame (ThrowFrame.))
(defn def-frame [term] (DefFrame. term))

(defn restore-frame [world mint] (RestoreFrame. world mint))
(defn restore-profile-frame [no-profile] (RestoreProfileFrame. no-profile))
(defn binders-frame [bound] (BindersFrame. bound))
(defn fn-frame
  "A frame that hands the returned value to (callback state value), which
   returns the next state."
  [callback]
  (FnFrame. callback))

(defn try-frame [catches finally-node env world mint] (TryFrame. catches finally-node env world mint))
(defn finally-value-frame [value] (FinallyValueFrame. value))
(defn finally-ret-frame [term env] (FinallyRetFrame. term env))
(defn finally-throw-frame [ex] (FinallyThrowFrame. ex))

(defn handle-frame [handlers return world mint] (HandleFrame. handlers return world mint))
(defn job-frame
  "A job's frame: {:job :meter :wallet :granted :parent-dyn :world :mint
   :on-return :on-throw} (klara.runtime.job)."
  [fields]
  (map->JobFrame fields))
(defn boundary-frame
  "The bottom frame of a nested machine. `deopt?`: compiled code called it,
   so an effect nobody inside handles leaves with the state (L4.exec.leave).
   `outer-k`: the continuation of the host call, for constructing."
  [deopt? outer-k]
  (BoundaryFrame. deopt? outer-k))

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
          (identical? x :handle) (if (contains? (.-handlers ^HandleFrame f) op) i (recur (next k) (inc i)))
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
