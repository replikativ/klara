(ns kmap.trap
  "Black-box probe of the D §4.3 symmetry trap: omit one interface at a time
  from a minimal map wrapper and observe = / hash / membership against a
  Clojure map. Each wrapper's own equiv uses the same rule as KMap."
  (:import [clojure.lang IPersistentMap MapEquivalence IHashEq Counted ILookup
            Associative IPersistentCollection Seqable]
           [java.util Map]))

(def map-equiv? @#'kmap.core/map-equiv?)
(def compute-hasheq @#'kmap.core/compute-hasheq)

(defmacro ^:private base-methods []
  `(~'IPersistentMap
    (~'assoc [~'_ k# v#] (.assoc ~'m k# v#))
    (~'assocEx [~'_ k# v#] (.assocEx ~'m k# v#))
    (~'without [~'_ k#] (.without ~'m k#))
    (~'containsKey [~'_ k#] (.containsKey ~'m k#))
    (~'entryAt [~'_ k#] (.entryAt ~'m k#))
    (~'valAt [~'_ k#] (.valAt ~'m k#))
    (~'valAt [~'_ k# nf#] (.valAt ~'m k# nf#))
    (~'count [~'_] (.count ~'m))
    (~'cons [~'_ o#] (.cons ~'m o#))
    (~'empty [~'_] (.empty ~'m))
    (~'equiv [~'this o#] (map-equiv? ~'this o#))
    (~'seq [~'_] (.seq ~'m))
    (~'iterator [~'_] (.iterator ~'m))))

(defmacro ^:private jmap-methods []
  `(~'Map
    (~'size [~'_] (.count ~'m))
    (~'isEmpty [~'_] (zero? (.count ~'m)))
    (~'get [~'_ k#] (.valAt ~'m k#))
    (~'containsValue [~'_ v#] (.containsValue ^Map ~'m v#))
    (~'keySet [~'_] (.keySet ^Map ~'m))
    (~'values [~'_] (.values ^Map ~'m))
    (~'entrySet [~'_] (.entrySet ^Map ~'m))
    (~'put [~'_ _# _#] (throw (UnsupportedOperationException.)))
    (~'remove [~'_ _#] (throw (UnsupportedOperationException.)))
    (~'putAll [~'_ _#] (throw (UnsupportedOperationException.)))
    (~'clear [~'_] (throw (UnsupportedOperationException.)))))

(defmacro ^:private hash-methods []
  `(~'IHashEq (~'hasheq [~'_] (unchecked-int (compute-hasheq ~'m)))
    ~'Object (~'hashCode [~'_] (.hashCode ~'m)) (~'equals [~'_ o#] (.equals ~'m o#))))

(defmacro ^:private variant [name me? jmap? hasheq?]
  `(deftype ~name [~(with-meta 'm {:tag 'clojure.lang.IPersistentMap})]
     ~@(macroexpand-1 '(base-methods))
     ~@(when me? '[MapEquivalence])
     ~@(when jmap? (macroexpand-1 '(jmap-methods)))
     ~@(if hasheq? (macroexpand-1 '(hash-methods))
           '[Object (hashCode [_] (.hashCode m)) (equals [_ o] (.equals m o))])))

(variant AllIfaces true true true)
(variant NoMapEquivalence false true true)
(variant NoJavaMap true false true)
(variant NoHashEq true true false)

(defn probe [ctor]
  (let [m {:a 1 :b [1 2]} x (ctor m)]
    {:clj=x (= m x) :x=clj (= x m)
     :hash= (= (hash m) (hash x))
     :x-in-set-of-clj (contains? #{m} x) :clj-in-set-of-x (contains? #{x} m)
     :vec [(= [m] [x]) (= [x] [m])]
     :.equals [(.equals ^Object m x) (.equals ^Object x m)]}))

(defn report []
  (into (sorted-map)
        {:1-all (probe ->AllIfaces)
         :2-no-MapEquivalence (probe ->NoMapEquivalence)
         :3-no-java.util.Map (probe ->NoJavaMap)
         :4-no-IHashEq (probe ->NoHashEq)}))
