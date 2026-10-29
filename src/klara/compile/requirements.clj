(ns klara.compile.requirements
  "Data-only requirements for the experimental pure scalar region path.
   These describe admission, not a certificate of compiler correctness."
  (:require [klara.world :as w] [klara.stage :as stage]))

(def version :scalar-region-v1)

(defn from-executable [exe input-layouts]
  (when-not (and (:name exe) (:code-id exe)
                 (= (count input-layouts) (get-in exe [:generic :arity]))
                 (every? #{:long} input-layouts)
                 (every? (fn [[kind value]]
                           (case kind
                             (:world :unhandled) true
                             :arity (= value (count input-layouts))
                             (:captures :statics) (= [] value)
                             false)) (:guards exe)))
    (throw (ex-info "requirements: unsupported executable contract" {})))
  {:version version
   :source {:name (:name exe) :code-id (:code-id exe)}
   :inputs input-layouts
   :world (set (filter #(= :world (first %)) (:guards exe)))
   :unhandled (into #{} (mapcat second) (filter #(= :unhandled (first %)) (:guards exe)))})

(defn well-formed? [r]
  (and (= #{:version :source :inputs :world :unhandled} (set (keys r)))
       (= version (:version r))
       (= #{:name :code-id} (set (keys (:source r))))
       (symbol? (get-in r [:source :name])) (string? (get-in r [:source :code-id]))
       (vector? (:inputs r)) (every? #{:long} (:inputs r))
       (set? (:unhandled r)) (every? keyword? (:unhandled r))
       (set? (:world r))
       (every? #(and (vector? %) (#{3 4} (count %)) (= :world (first %))
                     (symbol? (second %)) (or (string? (nth % 2)) (= :absent (nth % 2)))
                     (or (= 3 (count %)) (and (string? (nth % 2)) (string? (nth % 3)))))
               (:world r))))

(defn world-valid? [r root]
  (and (well-formed? r)
       (let [entry (w/entry* root (get-in r [:source :name]))]
         (and (= :def (:kind entry)) (not (w/pending? root entry))
              (= (:code-id entry) (get-in r [:source :code-id]))))
       (every? #(stage/guard-holds? % {:basis root}) (:world r))))

(defn call-valid? [r args outer-k]
  (and (well-formed? r)
       (= (count args) (count (:inputs r)))
       (every? #(instance? Long %) args)
       (stage/guard-holds? [:unhandled (:unhandled r)]
                         {:kont (mapcat identity outer-k)})))
