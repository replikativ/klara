(ns klara.world
  "Worlds as immutable values with versioned definitions (doc/01-core-v2.md
  §2, doc/05-architecture.md §2 'World').

  A ROOT is a persistent value

    {:version n                      ; bumped by every publication
     :defs    {sym entry}
     :rdeps   {sym #{dependent ..}}} ; reverse index over recorded reads

  and an entry is

    {:kind :def|:macro :value v :code core-term
     :code-id h      ; CodeId of the expanded definition
     :value-id h'    ; = code-id, or hash of code-id + definition-time
                     ;   value reads when evaluation consulted the world
     :reads #{..} :expansion-reads #{..} :eval-reads #{..}
     :version n :history [code-id ..] :form source}

  A WORLD is one reference to a root. Publication is a single CAS on that
  reference: there are no per-definition cells to keep in sync, so the
  race v0.world has (root swap, then cell reset, as two steps) cannot
  happen — a reader sees either the old root or the new one, never a mix.

  A FORK is a new reference initialised to the parent's current root and
  remembering it as :parent (the pinned snapshot). Structural sharing
  makes it free; writes to either side are invisible to the other.

  A FIBER pins a basis: reads resolve against the pinned root until
  raise-basis! moves the pin to the world's current root (Julia's
  latestworld as an explicit instruction).

  RECORDED READS. Expansion (and definition-time evaluation) consult the
  world only through `entry`, which notes a read into *reads* when it is
  bound. Read kinds, with the aspect they depend on:

    [:absent sym]         sym was NOT defined (negative lookup)
    [:def sym]            sym was a non-macro definition (resolve target;
                          late bound, so its code is not part of the read)
    [:macro sym value-id] sym was a macro with this transformer
    [:value sym value-id] sym's value was consumed (expansion-time call,
                          definition-time evaluation)

  A read is valid in a root iff the root still answers it the same way.")

;; ---------------------------------------------------------------------------
;; roots
;; ---------------------------------------------------------------------------

(def empty-root {:version 0 :defs {} :rdeps {}})

(defn entry* "Lookup without recording." [root sym] (get-in root [:defs sym]))

(def ^:dynamic *reads*
  "nil, or an atom holding the set of reads being recorded."
  nil)

(defn note-read! [r]
  (when *reads* (swap! *reads* conj r)))

(defn entry
  "Recorded lookup: notes the aspect the caller is about to depend on.
  aspect is :exists (expander: is it a def/macro?) or :value."
  [root sym aspect]
  (let [e (entry* root sym)]
    (note-read!
     (cond
       (nil? e)              [:absent sym]
       (= aspect :value)     [:value sym (:value-id e)]
       (= :macro (:kind e))  [:macro sym (:value-id e)]
       :else                 [:def sym]))
    e))

(defn read-valid? [root [kind sym h]]
  (let [e (entry* root sym)]
    (case kind
      :absent (nil? e)
      :def    (and e (= :def (:kind e)))
      :macro  (and e (= :macro (:kind e)) (= h (:value-id e)))
      :value  (and e (= h (:value-id e))))))

(defn invalid-reads [root reads]
  (into #{} (remove #(read-valid? root %)) reads))

(defn pending?
  "An entry whose recorded reads no longer hold in root: its expansion is
  stale and must not run while claiming this root (doc/01 §6)."
  [root e]
  (boolean (seq (invalid-reads root (:reads e)))))

(defn put-entry
  "Pure: install entry for sym in root, re-indexing reverse deps and
  bumping the version. Work is proportional to the entry's own reads,
  never to the number of dependents (gate R1)."
  [root sym e]
  (let [v (inc (:version root))
        old (entry* root sym)
        old-deps (into #{} (map second) (:reads old))
        new-deps (disj (into #{} (map second) (:reads e)) sym)
        root (reduce (fn [r d] (update-in r [:rdeps d] (fnil disj #{}) sym))
                     root old-deps)
        root (reduce (fn [r d] (update-in r [:rdeps d] (fnil conj #{}) sym))
                     root new-deps)
        hist (if (= (:code-id old) (:code-id e))
               (:history old [])
               (conj (:history old []) (:code-id e)))]
    (-> root
        (assoc :version v)
        (assoc-in [:defs sym] (assoc e :version v :history hist)))))

(defn dependents [root sym] (get-in root [:rdeps sym] #{}))

;; ---------------------------------------------------------------------------
;; worlds: one reference, one CAS
;; ---------------------------------------------------------------------------

(defrecord World [root parent])          ; root: atom of root value

(defn make-world
  ([] (make-world empty-root))
  ([root] (->World (atom root) nil)))

(defn snapshot "The world's current root (a value)." [w] @(:root w))

(defn publish!
  "THE publication protocol. f is a pure function root -> root'. Read the
  root, compute, compare-and-set; on conflict recompute against the new
  root. Returns the published root."
  [w f]
  (loop []
    (let [old @(:root w) new (f old)]
      (if (compare-and-set! (:root w) old new)
        new
        (recur)))))

(defn commit!
  "Optimistic publication of work computed against base with recorded
  reads. If the CAS loses, the work REBASES onto the new root when every
  read still holds there (no recomputation); otherwise returns ::retry
  and the caller recomputes. f is root -> root'."
  [w base reads f]
  (loop [b base]
    (let [new (f b)]
      (if (compare-and-set! (:root w) b new)
        new
        (let [cur @(:root w)]
          (if (empty? (invalid-reads cur reads))
            (recur cur)
            ::retry))))))

(defn fork
  "Snapshot fork: a new world over the parent's current root, which it
  pins as :parent."
  [w]
  (let [r (snapshot w)] (->World (atom r) r)))

;; ---------------------------------------------------------------------------
;; fibers: a pinned basis
;; ---------------------------------------------------------------------------

(defn fiber
  "A fiber over world w, pinned at w's current root."
  [w]
  {:world w :basis (atom (snapshot w))})

(defn basis [fib] @(:basis fib))

(defn raise-basis!
  "Move the fiber's pin to its world's current root; returns it."
  [fib]
  (reset! (:basis fib) (snapshot (:world fib))))
