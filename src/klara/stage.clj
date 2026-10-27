(ns klara.stage
  "The specialization cache (doc/01-core-v2 §3, §6; doc/research/C-staging
  §4.3; doc/06 §3 'guarded specialization').

  An EXECUTABLE is a cache entry for a closure's code:

    {:code-id h          ; CodeId of the fn term it specializes
     :guards #{g ..}     ; its assumption set
     :run f              ; host fn of the remaining arguments
     :certificate {..}}

  Guards, all checked on ENTRY (never later — live frames cannot be
  converted, so failure means the generic path runs from the start):

    [:world sym value-id]   the entry basis still answers sym this way
    [:world sym :absent]    the entry basis does not define sym
    [:arg i pred]           argument i satisfies pred (see `preds`)
    [:captures locals]      the closure captured exactly these values
    [:statics vals]         the partial application fixed these values

  The cache is keyed by (CodeId, assumption set). T0 consults it through
  klara.eval/*entry-hook*; no hit means the generic closure body runs.
  Deleting the cache therefore changes no result (gate R3): it only ever
  replaces a generic run by an executable whose guards hold, and the
  certificate obligation is that the two agree under those guards.

  Publication never touches the cache (gate R1): invalidation is lazy,
  by the [:world ..] guards on entry; `invalidate!` additionally sweeps
  entries whose recorded reads fail in a given root.

  INSTALL is certificate-checked. A certificate names the CodeId, the
  assumption set, the checker and its version, and provenance; install
  rejects it unless the CodeId and assumption set match the executable,
  the checker is trusted, and the digest over those fields is intact.
  S1 certificates are placeholders (checker :klara/trusted-handwritten
  or :klara/trivial); S3 replaces them by ansatz certificates."
  (:require [klara.core :as c]
            [klara.world :as w]
            [klara.eval :as ev]))

(def preds
  {:any (constantly true) :long #(instance? Long %) :double #(instance? Double %)
   :number number? :vector vector? :map map? :string string? :keyword keyword?})

(defn make-cache [] (atom {:entries {} :stats {:hits 0 :misses 0 :fallbacks 0}}))

(defn clear! "Delete every executable (R3)." [cache]
  (swap! cache assoc :entries {}) cache)

(defn stats [cache] (:stats @cache))
(defn executables [cache] (for [[_ m] (:entries @cache) [_ exe] m] exe))

;; ---------------------------------------------------------------------------
;; guards
;; ---------------------------------------------------------------------------

(defn guard-holds? [[kind a b] {:keys [basis captures statics args]}]
  (case kind
    :world (let [e (w/entry* basis a)]
             (if (= :absent b) (nil? e) (and e (= b (:value-id e)) (not (w/pending? basis e)))))
    :arg (and (< a (count args)) ((preds b) (nth args a)))
    :captures (= a captures)
    :statics (= a statics)))

(defn world-guards
  "[:world ..] guards for every global the code resolves, read in basis."
  [term basis]
  (into #{} (map (fn [s] (let [e (w/entry* basis s)]
                           [:world s (if e (:value-id e) :absent)])))
        (c/free-globals term)))

;; ---------------------------------------------------------------------------
;; certificates
;; ---------------------------------------------------------------------------

(def trusted-checkers #{:klara/trivial :klara/trusted-handwritten})

(defn- digest [{:keys [code-id assumptions checker checker-version]}]
  (c/sha256 (pr-str [code-id (sort-by pr-str assumptions) checker checker-version])))

(defn certify
  "A placeholder certificate for (code-id, guards)."
  [code-id guards checker provenance]
  (let [cert {:code-id code-id :assumptions (set guards) :checker checker
              :checker-version "s1-placeholder-0" :provenance provenance}]
    (assoc cert :digest (digest cert))))

(defn check-certificate
  "nil if the executable's certificate is acceptable, else a reason."
  [{:keys [code-id guards certificate]}]
  (let [{cid :code-id as :assumptions :keys [checker provenance] :as cert} certificate]
    (cond
      (nil? cert) :missing-certificate
      (not= cid code-id) :code-id-mismatch
      (not= as (set guards)) :assumption-mismatch
      (not (contains? trusted-checkers checker)) :untrusted-checker
      (nil? provenance) :missing-provenance
      (not= (:digest cert) (digest cert)) :digest-mismatch)))

(defn install!
  "Install exe after checking its certificate; throws on rejection."
  [cache exe]
  (when-let [reason (check-certificate exe)]
    (throw (ex-info (str "stage: certificate rejected: " (name reason))
                    {:reason reason :code-id (:code-id exe)})))
  (swap! cache assoc-in [:entries (:code-id exe) (set (:guards exe))] exe)
  exe)

;; ---------------------------------------------------------------------------
;; entry and invalidation
;; ---------------------------------------------------------------------------

(defn enter
  "The executable for closure f entered with statics and args under
  basis, or nil (generic fallback)."
  [cache f statics args basis]
  (when (ev/closure? f)
    (let [cid (c/code-id (ev/closure-term f))
          cands (get-in @cache [:entries cid])]
      (if (empty? cands)
        (do (swap! cache update-in [:stats :misses] inc) nil)
        (let [ctx {:basis basis :captures (ev/closure-locals f) :statics statics
                   :args (vec args)}
              exe (some (fn [[_ exe]] (when (every? #(guard-holds? % ctx) (:guards exe)) exe))
                        cands)]
          (swap! cache update-in [:stats (if exe :hits :fallbacks)] inc)
          (:run exe))))))

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

(defmacro with-cache
  "Evaluate body with cache as T0's entry hook."
  [cache & body]
  `(let [c# ~cache]
     (binding [ev/*entry-hook* (fn [f# s# a# b#] (enter c# f# s# a# b#))]
       ~@body)))

;; ---------------------------------------------------------------------------
;; producing executables
;; ---------------------------------------------------------------------------

(defn residual
  "The trivial specializer: an executable for closure f (optionally fixed
  statics) that runs the generic code, guarded by f's captures, statics
  and the world reads of its body in basis. By s-m-n it is correct by
  construction."
  ([f basis] (residual f [] basis))
  ([f statics basis]
   (let [term (ev/closure-term f)
         cid (c/code-id term)
         guards (cond-> (into #{[:captures (ev/closure-locals f)]} (world-guards term basis))
                  (seq statics) (conj [:statics (vec statics)]))]
     {:code-id cid :guards guards
      :run (fn [& args] (ev/call-generic f (into (vec statics) args)))
      :certificate (certify cid guards :klara/trivial {:specializer :klara.stage/residual})})))

(defn executable
  "A hand-written executable for closure f: run is a host fn trusted to
  agree with f's generic code under guards."
  [f guards run provenance]
  (let [cid (c/code-id (ev/closure-term f))]
    {:code-id cid :guards (set guards) :run run
     :certificate (certify cid guards :klara/trusted-handwritten provenance)}))
