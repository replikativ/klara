(ns klara.defs
  "Definitions: the expand -> evaluate -> publish pipeline and red-green
  invalidation with early cutoff (port of v0.defs + X1).

  define! expands a top-level form against the world's current root with
  the recording reader, evaluates the core term in T0 under that root
  with :mint nil (so the closures it creates are OPEN and run under
  their resolver's basis), records the world values that evaluation
  consumed, and publishes the entry with one optimistic CAS
  (klara.world/commit!: rebase when the reads still hold, else redo).

  A definition's dependencies are its recorded reads. There is no
  separate arity firewall: a runtime reference is a late-bound
  [:def s] read, which a body change of s never invalidates; only
  macro reads, value reads and negative lookups propagate.

  invalidate! walks dependents of a changed name over the root's reverse
  index, inside one expansion transaction published by a single CAS:
    green   - every recorded read still holds: nothing to do;
    cutoff  - re-expanded, same CodeId, and its value reads still hold:
              the entry keeps its value, only its reads are refreshed;
    stale   - re-evaluated (and re-expanded when its expansion reads
              broke); its dependents are examined in turn.
  Until then a dependent with broken reads is PENDING: resolving it in
  that root is an error, never a silent run of the old expansion."
  (:require [klara.core :as c]
            [klara.world :as w]
            [klara.expand :as x]
            [klara.eval :as ev]))

(defn- value-id [code-id eval-reads]
  (if (empty? eval-reads)
    code-id
    (c/sha256 (pr-str [code-id (sort-by pr-str eval-reads)]))))

(defn- evaluate
  "Definition-time evaluation: [value eval-reads]."
  [term root self]
  (let [reads (atom #{})
        v (binding [w/*reads* reads] (ev/run term {:basis root :mint nil}))]
    [v (into #{} (remove #(= self (second %))) @reads)]))

(defn- make-entry [{:keys [kind name term code-id reads]} root form]
  (let [[v ereads] (evaluate term root name)]
    {:kind kind :value v :code term :code-id code-id
     :value-id (value-id code-id ereads)
     :expansion-reads reads :eval-reads ereads :reads (into reads ereads)
     :form form}))

(defn define!
  "Define (def n e), (defmacro n [ps] body..) or a top-level macro call
  that expands to one of them, in world wo. Returns a summary."
  [wo form]
  (loop []
    (let [root (w/snapshot wo)
          res (x/expand-recorded form root)
          _ (when-not (#{:def :macro} (:kind res))
              (throw (ex-info "define!: not a definition" {:form form})))
          e (make-entry res root form)
          r (w/commit! wo root (:reads e) #(w/put-entry % (:name res) e))]
      (if (= ::w/retry r)
        (recur)
        (select-keys (assoc e :name (:name res)) [:name :kind :code-id :value-id :reads])))))

;; ---------------------------------------------------------------------------
;; invalidation
;; ---------------------------------------------------------------------------

(defn invalidate
  "Pure: process dependents of sym in root. Returns [root' report]."
  [root sym]
  (loop [frontier [sym] root root
         rep {:stale [] :green [] :cutoff [] :reexpanded []}]
    (if (empty? frontier)
      [root (update-vals rep (comp vec distinct))]
      (let [d (first frontier)
            deps (sort (w/dependents root d))
            [root rep more]
            (reduce
             (fn [[root rep more] dep]
               (let [e (w/entry* root dep)]
                 (cond
                   (empty? (w/invalid-reads root (:reads e)))
                   [root (update rep :green conj dep) more]

                   (seq (w/invalid-reads root (:expansion-reads e)))
                   (let [res (x/expand-recorded (:form e) root)
                         rep (update rep :reexpanded conj dep)]
                     (if (and (= (:code-id res) (:code-id e))
                              (empty? (w/invalid-reads root (:eval-reads e))))
                       [(w/put-entry root dep (assoc e :expansion-reads (:reads res)
                                                     :reads (into (:reads res) (:eval-reads e))))
                        (update rep :cutoff conj dep) more]
                       (let [e' (make-entry res root (:form e))]
                         [(w/put-entry root dep e') (update rep :stale conj dep)
                          (cond-> more (not= (:value-id e') (:value-id e)) (conj dep))])))

                   :else            ; only value reads broke: re-evaluate
                   (let [e' (make-entry (assoc e :term (:code e) :name dep
                                               :reads (:expansion-reads e))
                                        root (:form e))]
                     [(w/put-entry root dep e') (update rep :stale conj dep)
                      (cond-> more (not= (:value-id e') (:value-id e)) (conj dep))]))))
             [root rep []]
             deps)]
        (recur (into (vec (rest frontier)) more) root rep)))))

(defn invalidate!
  "Run invalidate as one expansion transaction: computed against a root,
  published with a single CAS (recomputed if another publication won)."
  [wo sym]
  (let [rep (volatile! nil)]
    (w/publish! wo (fn [root] (let [[r report] (invalidate root sym)]
                                (vreset! rep report) r)))
    @rep))

;; ---------------------------------------------------------------------------
;; reading and evaluating against a basis
;; ---------------------------------------------------------------------------

(defn lookup
  "The value of sym in root, bound to root (open closures are rebased)."
  [root sym]
  (let [e (w/entry* root sym)]
    (cond
      (nil? e) (throw (ex-info (str "unbound " sym) {:sym sym}))
      (w/pending? root e) (throw (ex-info (str sym " is pending re-expansion")
                                          {:sym sym :klara/error :pending}))
      :else (ev/rebase (:value e) root))))

(defn eval-form
  "Expand and evaluate an expression form under basis root."
  ([root form] (eval-form root form nil))
  ([root form fib]
   (ev/run (x/expand-expr form root) {:basis root :fiber fib})))

(defn eval-in
  "Expand and evaluate form in fiber fib, under its pinned basis."
  [fib form]
  (eval-form (w/basis fib) form fib))
