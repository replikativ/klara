(ns klara.runtime.world
  "Worlds as values (spec/L1-worlds.md): creation, definition, lookup,
  footprints and slices. Pure functions; the session (klara.runtime.session)
  owns the only mutable cell."
  (:require [klara.lang.term :as t]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value World Definition]))

(def ^:private world-ids (java.util.concurrent.atomic.AtomicLong. 0))
(def ^:private generations (java.util.concurrent.atomic.AtomicLong. 0))

(defn next-generation [] (.incrementAndGet generations))

(defn- new-id [] (str "w" (.incrementAndGet world-ids)))

(defn empty-world [] (World. (new-id) nil {} {} nil {}))

(defn id [^World w] (.-id w))
(defn defs [^World w] (.-defs w))
(defn namespaces [^World w] (.-namespaces w))
(defn slice? [^World w] (some? (.-footprint w)))

(defn lookup
  "The definition of `q` in `w`, or nil. In a slice, a name outside the
   footprint is an internal error (L1.slice.missing)."
  [^World w q]
  (let [d (get (.-defs w) q)]
    (when (and (nil? d) (.-footprint w) (not (contains? (.-footprint w) q)))
      (throw (ex-info (str "slice of " (.-id w) " has no " q)
                      {:rule :L1.slice.missing :name q :world (.-id w)})))
    d))

(defn generation [w q] (some-> (lookup w q) :generation))

(defn delta
  "What `w` changed relative to the world it was forked or published from:
   {:defs {q base-definition} :namespaces {ns base-record}}. Only the base
   entries of changed names are kept, never the base world itself
   (design/01-lifetimes.md#roots)."
  [^World w] (.-delta w))

(defn fork
  "A new world with the same definitions, a new identity and no changes yet (L3.job.run)."
  [^World w]
  (World. (new-id) (.-id w) (.-defs w) (.-namespaces w) nil {}))

(defn- note [delta kind k base]
  (if (contains? (get delta kind) k) delta (assoc-in delta [kind k] base)))

(defn put-definition
  "A new world equal to `w` except that `q` is defined by `d` (L1.world.define)."
  [^World w q d]
  (World. (new-id) (.-id w) (assoc (.-defs w) q d) (.-namespaces w) nil
          (note (.-delta w) :defs q (get (.-defs w) q))))

(defn definition
  [q {:keys [form term value macro?]}]
  (Definition. q form term value (next-generation)
               (when term (t/globals term)) (boolean macro?)))

(defn update-namespace
  "A new world whose namespace record for `ns` is (f record)."
  [^World w ns f]
  (World. (new-id) (.-id w) (.-defs w) (update (.-namespaces w) ns f) nil
          (note (.-delta w) :namespaces ns (get (.-namespaces w) ns))))

(defn ns-info [^World w ns] (get (.-namespaces w) ns))

(defn apply-delta
  "Apply the changes of `changed` to `current` (L1.session.publish). A
   change conflicts if `current` no longer has the base entry the change
   was made from. Returns the new world (with no pending changes), or nil
   on a conflict."
  [^World changed ^World current]
  (let [{dd :defs dn :namespaces} (delta changed)
        conflict? (or (some (fn [[q base]] (not (identical? base (get (defs current) q)))) dd)
                      (some (fn [[n base]] (not (identical? base (get (namespaces current) n)))) dn))]
    (when-not conflict?
      (World. (new-id) (id current)
              (reduce (fn [m q] (if-let [d (get (defs changed) q)] (assoc m q d) (dissoc m q)))
                      (defs current) (keys dd))
              (reduce (fn [m n] (assoc m n (get (namespaces changed) n))) (namespaces current) (keys dn))
              nil {}))))

(defn changed-names
  "Names whose definitions differ between two worlds (for history summaries)."
  [^World a ^World b]
  (into #{} (filter #(not (identical? (get (defs a) %) (get (defs b) %))))
        (into (set (keys (defs a))) (keys (defs b)))))

;; ---------------------------------------------------------------------------
;; Footprints and slices (L1.slice.*)

(def dynamic-operations
  "Operations whose presence makes a footprint unknowable (L1.slice.dynamic)."
  '#{klara.stage/run klara.world/current klara.world/advance klara.world/get
     klara.world/in klara.world/define klara.kernel/require})

(defn- dynamic? [term]
  (some #(and (= :host (:op %)) (contains? dynamic-operations (:name %))) (t/nodes term)))

(defn footprint
  "The footprint of `q` in `w`: the names its definition can reach, or nil
   when the definition uses a dynamic world operation."
  [^World w q]
  (loop [todo [q] seen #{}]
    (if-let [[n & more] (seq todo)]
      (if (contains? seen n)
        (recur more seen)
        (let [d (get (defs w) n)]
          (cond
            (nil? d) (recur more (conj seen n))
            (and (:term d) (dynamic? (:term d))) nil
            :else (recur (into (vec more) (:reads d)) (conj seen n)))))
      seen)))

(defn slice
  "`w` restricted to `names`; the same world identity (L1.slice.resolve).
   With nil names the whole world is returned."
  [^World w names]
  (if (nil? names)
    w
    (World. (.-id w) (.-parent w) (select-keys (.-defs w) names) {} (set names) {})))

(defn pin
  "The value of `q` in `w`, with a closure pinned to the slice of `w` it can
   reach (L1.context.get, design/01-lifetimes.md#retention-is-proportional-to-use-footprints)."
  [^World w q]
  (let [d (lookup w q)]
    (when (nil? d)
      (throw (ex-info (str "unable to resolve " q " in " (id w)) {:rule :L1.resolve.unbound :name q})))
    (let [val (:value d)]
      (if (and (v/closure? val) (nil? (.-basis ^klara.runtime.value.Closure val)))
        (v/rebase val (if (slice? w) w (slice w (footprint w q))))
        val))))
