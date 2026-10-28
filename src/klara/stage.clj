(ns klara.stage
  "The specialization cache (doc/01-core-v2 §3, §6; doc/research/C-staging
  §4.3; doc/06 §3 'guarded specialization').

  An EXECUTABLE is a cache entry for a closure's code:

    {:code-id h          ; CodeId of the fn term it specializes
     :guards #{g ..}     ; its assumption set
     :run f              ; a host fn of the arguments (must not perform
                         ;   Klara effects: it is a host frame), or
     :klara g :prefix [..] ; Klara code entered in the same machine
     :certificate {..}}

  Guards, all checked on ENTRY (a guard on an intermediate value is a
  speculation point inside the body, below):

    [:world sym value-id]   the entry basis still answers sym this way
    [:world sym :absent]    the entry basis does not define sym
    [:arg i pred]           argument i satisfies pred (see `preds`)
    [:captures locals]      the closure captured exactly these values
    [:statics vals]         the partial application fixed these values
    [:unhandled ops]        no dynamic handler for any of ops is active in
                            the caller's continuation (the reference
                            handler answers them, as the executable assumes)

  The cache is keyed by (CodeId, assumption set). T0 consults it through
  klara.eval/*entry-hook*; no hit means the generic closure body runs.
  Deleting the cache therefore changes no result (gate R3): it only ever
  replaces a generic run by an executable whose guards hold, and the
  certificate obligation is that the two agree under those guards.

  Publication never touches the cache (gate R1): invalidation is lazy,
  by the [:world ..] guards on entry; `invalidate!` additionally sweeps
  entries whose recorded reads fail in a given root.

  PER-ROOT VALIDITY (S7). Roots are immutable, so whether an
  executable's [:world ..] guards hold depends only on the root. Entry
  checks them once per (executable, root) and memoizes the verdict on
  the installed executable (a few most recent roots, held weakly and
  compared by identity); every later entry under that root costs one
  identity comparison. Publication does no work for executables, and no
  dependents are walked: the cost moves to the first entry under a new
  root, once per executable entered there. Runtime guards ([:arg ..]
  [:captures ..] [:statics ..] [:unhandled ..]) are checked on every
  entry.

  SPECULATION AND DEOPT (S7). A speculative executable (`speculative`)
  carries FRAME STATES: descriptions of the generic code's T0 state at a
  guard point inside the body. When the guard fails, the code calls
  deopt! with the frame state's index and its live values; klara.eval
  rebuilds the generic machine state (environment, continuation frames,
  pending handlers, elided closures and instances) and resumes T0 there,
  so effects already performed are not repeated. See klara.eval
  `materialize` for the frame-state format. Deopts are counted as
  FEEDBACK keyed by (CodeId, site): monotone counters, capped, consulted
  by `speculate?`.

  INSTALL is certificate-checked. A certificate names the CodeId, the
  assumption set, the checker and its version, and provenance; install
  rejects it unless the CodeId and assumption set match the executable,
  the checker is trusted, and the digest over those fields is intact.
  Checkers are a registry (`register-checker!`): a checker is a function
  of the executable returning nil or a rejection reason. S1's
  :klara/trivial and :klara/trusted-handwritten accept after the common
  checks; S3 registers :ansatz/kernel (klara.fusion), which re-elaborates
  the source and rechecks the theorem in the ansatz kernel."
  (:require [klara.authority :as a]
            [klara.core :as c]
            [klara.world :as w]
            [klara.eval :as ev])
  (:import [java.lang.ref WeakReference]
           [java.util.concurrent ConcurrentHashMap]
           [java.util.concurrent.atomic AtomicLong LongAdder]))

(defn nat-list?
  "nil, or a vector or list (realized, so checking it runs no code) whose
  elements are non-negative Longs: the runtime check of the shape claim
  (List Nat) on the JVM."
  [x]
  (or (nil? x)
      (and (or (vector? x) (list? x))
           (every? #(and (instance? Long %) (>= (long %) 0)) x))))

(def preds
  {:any (constantly true) :long #(instance? Long %) :double #(instance? Double %)
   :number number? :vector vector? :map map? :string string? :keyword keyword?
   :nat-list nat-list?})

;; ---------------------------------------------------------------------------
;; feedback: monotone capped counters keyed by (CodeId, site)
;; ---------------------------------------------------------------------------

(def feedback-cap
  "Counters saturate here: every chain of observations is finite."
  1000000)

(def ^:dynamic *feedback*
  "Current cache feedback for emitted guards; nil outside with-cache.
  This predictor never licenses an unchecked fast path."
  nil)

(defn make-feedback [] (ConcurrentHashMap.))

(defn observe!
  "Count one observation of kind (e.g. :deopt) at site [code-id site-id].
  Monotone: counters only grow, and saturate at feedback-cap."
  [^ConcurrentHashMap fb site kind]
  (let [^AtomicLong n (.computeIfAbsent fb [site kind]
                                        (reify java.util.function.Function
                                          (apply [_ _] (AtomicLong.))))]
    (when (< (.get n) feedback-cap) (.incrementAndGet n))
    nil))

(defn observed
  "The count of kind at site (0 if never observed)."
  [^ConcurrentHashMap fb site kind]
  (if-let [^AtomicLong n (.get fb [site kind])] (min feedback-cap (.get n)) 0))

(defn feedback
  "Snapshot {[site kind] n}."
  [^ConcurrentHashMap fb]
  (into {} (map (fn [[k ^AtomicLong n]] [k (min feedback-cap (.get n))])) fb))

(defn join-feedback
  "The join of two snapshots (pointwise max): how a fork's feedback
  would be merged back into its parent's."
  [a b]
  (merge-with max a b))

(defn speculate?
  "The speculation decision: speculate at site unless it has deopted
  max-deopts times (default 3); then the site is poisoned for good,
  since counters never decrease."
  ([fb site] (speculate? fb site 3))
  ([fb site max-deopts] (< (observed fb site :deopt) max-deopts)))

;; ---------------------------------------------------------------------------
;; the cache
;; ---------------------------------------------------------------------------

(def ^:private counter-keys [:hits :misses :fallbacks :revalidations :deopts])

(defn make-cache []
  (atom {:entries {}
         :counters (zipmap counter-keys (repeatedly #(LongAdder.)))
         :feedback (make-feedback)}))

(defn- count! [c k] (.increment ^LongAdder (get (:counters c) k)))

(defn clear! "Delete every executable (R3)." [cache]
  (swap! cache assoc :entries {}) cache)

(defn stats
  "{:hits :misses :fallbacks :revalidations :deopts}. Revalidations count
  (executable, root) pairs whose world guards were actually checked."
  [cache]
  (update-vals (:counters @cache) #(.sum ^LongAdder %)))

(defn cache-feedback [cache] (:feedback @cache))
(defn executables [cache] (for [[_ m] (:entries @cache) [_ exe] m] exe))

;; ---------------------------------------------------------------------------
;; guards
;; ---------------------------------------------------------------------------

(defn- dynamically-handled? [kont ops]
  (some (fn [f] (and (= :handle (:tag f)) (= :dynamic (:mode f))
                     (some #(contains? (:clauses f) %) ops)))
        kont))

(defn guard-holds? [[kind a b] {:keys [basis captures statics args kont]}]
  (case kind
    :world (let [e (w/entry* basis a)]
             (if (= :absent b) (nil? e) (and e (= b (:value-id e)) (not (w/pending? basis e)))))
    :arg (and (< a (count args)) ((preds b) (nth args a)))
    :captures (= a captures)
    :statics (= a statics)
    :unhandled (not (dynamically-handled? kont a))))

(defn world-guards
  "[:world ..] guards for every global the code resolves, read in basis."
  [term basis]
  (into #{} (map (fn [s] (let [e (w/entry* basis s)]
                           [:world s (if e (:value-id e) :absent)])))
        (c/free-globals term)))

;; ---------------------------------------------------------------------------
;; certificates
;; ---------------------------------------------------------------------------

(defonce ^{:doc "checker keyword -> (fn [exe]) returning nil (accept) or a reason."}
  checkers
  (atom {:klara/trivial (constantly nil)
         :klara/trusted-handwritten (constantly nil)}))

(defn register-checker! [k f] (swap! checkers assoc k f) k)

(defn digest
  "Hash over every certificate field except :digest and :payload (the
  payload holds host objects such as kernel terms; a checker binds them to
  hashed fields itself)."
  [cert]
  (c/sha256 (binding [*print-meta* false *print-length* nil *print-level* nil]
              (pr-str (c/canonical (dissoc cert :digest :payload))))))

(defn certify
  "A placeholder certificate for (code-id, guards)."
  [code-id guards checker provenance]
  (let [cert {:code-id code-id :assumptions (set guards) :checker checker
              :checker-version "s1-placeholder-0" :provenance provenance}]
    (assoc cert :digest (digest cert))))

(defn frame-states-digest
  "Hash of an executable's frame states and generic code (nil if none);
  certified with the executable, so they cannot be swapped afterwards."
  [{:keys [frame-states generic]}]
  (when frame-states
    (c/sha256 (binding [*print-meta* false *print-length* nil *print-level* nil]
                (pr-str (c/canonical [generic frame-states]))))))

;; frame-state validation --------------------------------------------------------

(defn- binders-entering
  "How many binders a step from node into its key k pushes."
  [node k]
  (case [(:op node) k]
    [:fn :body] (+ (:arity node) (if (:rest? node) 1 0))
    [:let :body] 1
    [:handle :body] 1
    ([:letrec :inits] [:letrec :body]) (count (:inits node))
    0))

(defn scope-depth
  "Number of locals the term at path (get-in style, from the fn term)
  sees beyond the closure's captures."
  [term path]
  (loop [node term path (seq path) d 0]
    (if-not path
      d
      (let [k (first path)]
        (recur (get node k) (next path) (+ d (long (if (map? node) (binders-entering node k) 0))))))))

(defn- slots-of
  "Every slot of a frame state (nested ones included)."
  [fs]
  (let [top (concat (:env fs)
                    (when (= :ret (first (:at fs))) [(second (:at fs))])
                    (mapcat (fn [fr] (concat (when (vector? (:env fr)) (:env fr)) (:vals fr)
                                             (vals (:clauses fr)) (keep fr [:instance :return])))
                            (:kont fs)))]
    (mapcat #(tree-seq (fn [sl] (= :vector (first sl))) second %) top)))

(def ^:private frame-ops
  "Frame template tag -> the ops of the node such a frame belongs to."
  {:let #{:let} :if #{:if} :handle #{:handle}
   :list #{:app :prim :perform :handle :specialize}})

(defn- frame-state-error
  "nil, or why frame state fs cannot describe a state of generic code
  (the fn term) whose closures capture ncap locals."
  [generic ncap fs]
  (let [node? #(and (map? %) (contains? c/forms (:op %)))
        at (fn [p] (get-in generic p))
        [mode x] (:at fs)]
    (cond
      (not (#{:eval :ret} mode)) [:bad-position (:at fs)]
      (and (= :eval mode) (not (node? (at x)))) [:no-node x]
      (and (= :eval mode) (not= (count (:env fs)) (+ ncap (scope-depth generic x))))
      [:env-shape {:path x :expected (+ ncap (scope-depth generic x)) :actual (count (:env fs))}]
      :else
      (or (some (fn [{:keys [tag path env fn] :as fr}]
                  (let [g (or fn generic) nd (get-in g path)]
                    (cond
                      (not (frame-ops tag)) [:bad-frame tag]
                      (not (node? nd)) [:no-node path]
                      (not ((frame-ops tag) (:op nd))) [:frame-node-mismatch tag (:op nd)]
                      (and (integer? env) (nil? fn)
                           (not= env (+ ncap (scope-depth generic path))))
                      [:frame-env-shape {:path path :expected (+ ncap (scope-depth generic path)) :actual env}]
                      (and (integer? env) (> env (count (:env fs)))) [:frame-env-shape {:path path}])))
                (:kont fs))
          (some (fn [[kind v :as sl]]
                  (cond
                    (not (#{:live :const :local :closure :letrec :instance :vector} kind)) [:bad-slot sl]
                    ;; an authority baked into a frame state would be revived by
                    ;; every deopt: authorities reach a frame state only as live values
                    (and (= :const kind) (some a/auth? (tree-seq coll? seq v))) [:authority-constant]))
                (slots-of fs))))))

(defn frame-states-error
  "nil if every frame state of exe is well-shaped, else a reason."
  [{:keys [code-id generic frame-states guards]}]
  (when frame-states
    (let [ncap (some (fn [[k v]] (when (= :captures k) v)) guards)]
      (cond
        (not= code-id (some-> generic c/code-id)) :generic-mismatch
        (nil? ncap) :missing-captures-guard
        :else (some (fn [[i fs]] (when-let [e (frame-state-error generic (count ncap) fs)]
                                   (ex-info "bad frame state" {:index i :error e})))
                    (map-indexed vector frame-states))))))

(defn check-certificate
  "nil if the executable's certificate is acceptable, else a reason."
  [{:keys [code-id guards certificate] :as exe}]
  (let [{cid :code-id as :assumptions :keys [checker provenance] :as cert} certificate]
    (cond
      (nil? cert) :missing-certificate
      (not= cid code-id) :code-id-mismatch
      (not= as (set guards)) :assumption-mismatch
      (not= (:frame-states cert) (frame-states-digest exe)) :frame-state-mismatch
      (not (contains? @checkers checker)) :untrusted-checker
      (nil? provenance) :missing-provenance
      (not= (:digest cert) (digest cert)) :digest-mismatch
      :else ((get @checkers checker) exe))))

(defn- world-guard? [g] (= :world (nth g 0)))

(defn- prepare
  "The installed form: guards split into world guards (a function of the
  root, memoized per root) and runtime guards, plus the memo."
  [exe]
  (let [gs (vec (:guards exe))]
    (assoc exe
           ::world (filterv world-guard? gs)
           ::runtime (filterv (complement world-guard?) gs)
           ::memo (atom []))))

(defn install!
  "Install exe after checking its certificate (and frame states); throws
  on rejection."
  [cache exe]
  (when-let [reason (or (check-certificate exe)
                        (when-let [e (frame-states-error exe)]
                          (if (keyword? e) e :bad-frame-state)))]
    (throw (ex-info (str "stage: certificate rejected: " (name reason))
                    (cond-> {:reason reason :code-id (:code-id exe)}
                      (= :bad-frame-state reason) (merge (ex-data (frame-states-error exe)))))))
  (swap! cache assoc-in [:entries (:code-id exe) (set (:guards exe))] (prepare exe))
  exe)

;; ---------------------------------------------------------------------------
;; entry and invalidation
;; ---------------------------------------------------------------------------

;; CodeIds of closure terms on the entry path: a small direct-mapped table
;; keyed by term identity, so entry does not hash or compare the term
;; (code-id's own memo compares equal-but-distinct terms structurally).
(def ^:private cid-table (object-array 512))

(defn- term-code-id [t]
  (let [i (bit-and (System/identityHashCode t) 511)
        e (aget ^objects cid-table i)]
    (if (and e (identical? t (nth e 0)))
      (nth e 1)
      (let [cid (c/code-id t)]
        (aset ^objects cid-table i [t cid])
        cid))))

(def ^:private memo-size 4)

(defn- memo-verdict [entries root]
  (loop [es (seq entries)]
    (when es
      (let [[^WeakReference r v] (first es)]
        (if (identical? root (.get r)) v (recur (next es)))))))

(defn valid-in?
  "Do exe's world guards hold in root? Checked once per (exe, root) and
  memoized on the installed executable; c (the cache value) counts the
  checks actually performed."
  [c exe root]
  (let [memo (::memo exe)
        v (memo-verdict @memo root)]
    (if v
      (identical? v :valid)
      (let [ok (every? #(guard-holds? % {:basis root}) (::world exe))
            verdict (if ok :valid :invalid)]
        (count! c :revalidations)
        (swap! memo (fn [es] (into [[(WeakReference. root) verdict]]
                                   (comp (remove (fn [[^WeakReference r]] (nil? (.get r))))
                                         (take (dec memo-size)))
                                   es)))
        ok))))

(defn enter
  "The executable for closure f entered with statics and args under
  basis with continuation kont, or nil (generic fallback)."
  [cache f statics args basis kont]
  (when (ev/closure? f)
    (let [c @cache
          cands (get (:entries c) (term-code-id (ev/closure-term f)))]
      (if (empty? cands)
        (do (count! c :misses) nil)
        (let [ctx {:basis basis :captures (ev/closure-locals f) :statics statics
                   :args (vec args) :kont kont}
              exe (some (fn [[_ exe]]
                          (when (and (valid-in? c exe basis)
                                     (every? #(guard-holds? % ctx) (::runtime exe)))
                            exe))
                        cands)]
          (count! c (if exe :hits :fallbacks))
          exe)))))

(defn invalidate!
  "Drop executables whose [:world ..] guards fail in root. Returns the
  number dropped."
  [cache root]
  (let [n (volatile! 0)
        ok? (fn [exe] (every? (fn [[k :as g]] (or (not= :world k) (guard-holds? g {:basis root})))
                              (:guards exe)))]
    (swap! cache update :entries
           (fn [es] (vreset! n 0)
             (into {} (keep (fn [[cid m]]
                              (let [m' (into {} (filter (fn [[_ exe]] (or (ok? exe) (do (vswap! n inc) false)))) m)]
                                (when (seq m') [cid m']))))
                   es)))
    @n))

(defn record-deopt!
  "T0's deopt hook for cache: count the deopt and observe it as feedback
  at (CodeId, the frame state's :site)."
  [cache exe fs _live]
  (let [c @cache]
    (count! c :deopts)
    (some-> (:deopts exe) (swap! inc))
    (observe! (:feedback c) [(:code-id exe) (:site fs)] :deopt)))

(defmacro with-cache
  "Evaluate body with cache as T0's entry hook (and deopt hook)."
  [cache & body]
  `(let [c# ~cache]
     (binding [*feedback* (cache-feedback c#)
               ev/*entry-hook* (fn [f# s# a# b# k#] (enter c# f# s# a# b# k#))
               ev/*deopt-hook* (fn [e# fs# l#] (record-deopt! c# e# fs# l#))]
       ~@body)))

;; ---------------------------------------------------------------------------
;; producing executables
;; ---------------------------------------------------------------------------

(defn residual
  "The trivial specializer: an executable for closure f (optionally fixed
  statics) that enters the generic code in the same machine, guarded by
  f's captures, statics and the world reads of its body in basis. By
  s-m-n it is correct by construction, and effects inside keep working."
  ([f basis] (residual f [] basis))
  ([f statics basis]
   (let [term (ev/closure-term f)
         cid (c/code-id term)
         guards (cond-> (into #{[:captures (ev/closure-locals f)]} (world-guards term basis))
                  (seq statics) (conj [:statics (vec statics)]))]
     {:code-id cid :guards guards
      :klara f :prefix (vec statics)
      :certificate (certify cid guards :klara/trivial {:specializer :klara.stage/residual})})))

(defn executable
  "A hand-written executable for closure f: run is a host fn trusted to
  agree with f's generic code under guards."
  [f guards run provenance]
  (let [cid (c/code-id (ev/closure-term f))]
    {:code-id cid :guards (set guards) :run run
     :certificate (certify cid guards :klara/trusted-handwritten provenance)}))

(def deopt!
  "Called by a host executable (:run) at a failed guard: (deopt! i live)
  leaves the executable and resumes generic T0 at its frame state i,
  with live the vector of values the frame state's [:live j] slots
  name. Never returns."
  ev/deopt!)

(defn speculative
  "A speculative executable for closure f. code is either a Klara
  closure entered in the same machine (effects keep working; a failed
  guard performs (deopt! i [live ..]), the surface form of `speculate`)
  or a host fn of the arguments (it may call klara.stage/deopt!, but
  must perform no Klara effect). frame-states is a vector; frame state i
  describes where generic f's code resumes when deopt i is taken (format:
  klara.eval/materialize). guards must include [:captures ..]. The
  obligation, carried by the trusted-handwritten certificate, is that
  code agrees with f under guards until a deopt, and that each frame
  state is exact: the state it rebuilds is the one f's generic code is
  in at that point of the same run."
  [f code frame-states guards provenance]
  (let [term (ev/closure-term f)
        cid (c/code-id term)
        klara? (ev/closure? code)]
    (when (and klara? (not (identical? (ev/closure-basis code) (ev/closure-basis f))))
      (throw (ex-info "stage: a speculative closure must have its generic closure's basis" {})))
    (let [exe (cond-> {:code-id cid :guards (set guards) :generic term
                       :frame-states (vec frame-states)}
                klara? (assoc :klara code :prefix [])
                (not klara?) (assoc :run code))]
      (assoc exe :certificate
             (let [cert (-> {:code-id cid :assumptions (set guards)
                             :checker :klara/trusted-handwritten
                             :checker-version "s7-placeholder-0" :provenance provenance}
                            (assoc :frame-states (frame-states-digest exe)))]
               (assoc cert :digest (digest cert)))))))
