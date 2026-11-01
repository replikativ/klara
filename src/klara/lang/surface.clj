(ns klara.lang.surface
  "Clojure surface forms Klara implements as macros over Core
  (spec/L0-core.md#surface): vswap! and defrecord."
  (:require [klara.lang.builtins :as b]))

(defn- fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; vswap! is a macro in Clojure: (vswap! v f & args) = (vreset! v (f @v args..))
(b/register! 'klara.core/vswap!
             {:kind :macro
              :fn (fn [[_ v f & args] _env]
                    (let [x (gensym "v")]
                      (list 'clojure.core/let [x v]
                            (list 'clojure.core/vreset! x (list* f (list 'clojure.core/deref x) args)))))})

;; defrecord (L0.surface.defrecord): a record is a map of its fields, tagged
;; with its type in metadata; ->Name and map->Name construct it.
(b/register! 'klara.core/defrecord
             {:kind :macro
              :fn (fn [[_ nm fields & impls] env]
                    (when (seq impls)
                      (fail :L0.surface.defrecord "protocol implementations in defrecord are not supported yet"))
                    (let [tag (symbol (str (:ns env)) (name nm))
                          ks (mapv (comp keyword name) fields)
                          m (gensym "m")]
                      (list 'do
                            (list 'def nm (list 'quote tag))
                            (list 'defn (symbol (str "->" nm)) (vec fields)
                                  (list 'clojure.core/with-meta (zipmap ks fields) {:klara/record (list 'quote tag)}))
                            (list 'defn (symbol (str "map->" nm)) [m]
                                  (list 'clojure.core/with-meta (list 'clojure.core/merge (zipmap ks (repeat nil)) m)
                                        {:klara/record (list 'quote tag)})))))})
