(ns klara.compile.host
  "Clojure/JVM realization of Core primitives, shared by hosted emitters."
  (:require [klara.core :as core]))

(defn- known-key? [form]
  (and (seq? form) (contains? #{'quote 'clojure.core/quote} (first form))
       (= 2 (count form))
       (let [x (second form)]
         (or (nil? x) (boolean? x) (instance? Long x) (instance? Double x)
             (keyword? x) (symbol? x) (string? x)))))

(defn primitive-form [name arguments]
  (if (= name 'literal-map)
    (let [arguments (vec arguments) keys (take-nth 2 arguments)
          _ (when (odd? (count arguments))
              (throw (ex-info "literal-map needs key/value pairs" {:reason :unsupported-region})))
          unique? (or (<= (count arguments) 2)
                      (and (every? known-key? keys)
                           (= (count keys) (count (distinct (map second keys))))))
          array (with-meta (gensym "literal") {:tag 'objects})]
      ;; This private array is filled once in source order, then handed to RT.
      ;; It is never exposed or mutated after the persistent map is created.
      (if (empty? arguments) 'clojure.lang.PersistentArrayMap/EMPTY
        `(let [~array (object-array ~(count arguments))]
           ;; Clojure's polymorphic aset can fall back to reflection when the
           ;; value is primitive even with an Object[] target. Select the
           ;; exact reference-array overload, which boxes only the value.
           ~@(map-indexed
               (fn [i form]
                 (list (with-meta 'clojure.lang.RT/aset
                         {:param-tags ['objects 'int 'java.lang.Object]}) array i form))
               arguments)
           (~(if unique? 'clojure.lang.RT/mapUniqueKeys 'clojure.lang.RT/map) ~array))))
    (list* (core/primitive-symbol name) arguments)))

(defn evaluate
  "Generated host code resolves under the backend namespace, independently of
   the caller's host refers/aliases and of guest module definitions."
  [form]
  (binding [*ns* (the-ns 'klara.compile.host)] (eval form)))
