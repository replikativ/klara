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

;; defrecord (L0.surface.defrecord): a host record class, as in Clojure, so a
;; field is read directly; Name is the class, ->Name and map->Name construct.
(b/register! 'klara.core/defrecord
             {:kind :macro
              :fn (fn [[_ nm fields & impls] env]
                    (when (seq impls)
                      (fail :L0.surface.defrecord "protocol implementations in defrecord are not supported yet"))
                    (let [q (symbol (str (:ns env)) (name nm))
                          r (gensym "record")]
                      (list 'clojure.core/let [r (list 'klara.core/record-type (list 'quote q) (list 'quote (vec fields)))]
                            (list 'def nm (list 'clojure.core/get r :class))
                            (list 'def (symbol (str "->" nm)) (list 'clojure.core/get r :new))
                            (list 'def (symbol (str "map->" nm)) (list 'clojure.core/get r :create))
                            (list 'clojure.core/get r :class))))})
