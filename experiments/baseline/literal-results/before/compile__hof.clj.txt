(ns klara.compile.hof
  "Recognize exact public host operators. No stage of a lazy pipeline is
  fused across another: Clojure's operators own chunking and traversal."
  (:require [klara.compile.ir :as ir] [klara.core :as c]))

(def operators '#{map filter mapv reduce some every? into range reduced reduced? unreduced})
(def callbacks '#{map filter mapv reduce some every?})

(def host-roots
  ;; Public Var values, never implementation sources. Rebinding these Vars
  ;; invalidates entry before a rewritten operator can retain a callback.
  (into {} (for [n (into operators (keys c/prims))
                 :let [s (symbol "clojure.core" (name n))]]
             [s @(requiring-resolve s)])))

(defn run [term]
  (let [changes (atom 0) guards (atom #{})]
    (letfn [(go [t]
              (let [t (ir/map-children go t) [head & args] (:args t)
                    sym (:datum head) n (when (symbol? sym) (symbol (name sym)))]
                (if (and (= :perform (:op t)) (nil? (:target t))
                         (= :host/call (:name t)) (= :quote (:op head))
                         (symbol? sym) (= "clojure.core" (namespace sym)) (operators n))
                  (do (swap! changes inc)
                      (swap! guards conj [:host-root sym (host-roots sym)])
                      ;; Function-valued primitives are recognized only in this
                      ;; callback position, at the licensed fixed arity.
                      (let [arity (if (= 'reduce n) 2 1)
                            f (first args)
                            p (get-in f [:args 0 :datum])
                            primitive (when (and (= :perform (:op f)) (nil? (:target f))
                                                 (= :host/var (:name f)) (symbol? p)
                                                 (= "clojure.core" (namespace p)))
                                        (symbol (name p)))
                            args (if (and (callbacks n) (contains? c/prims primitive))
                                   (let [_ (swap! guards conj [:host-root p (host-roots p)])
                                         ps (vec (repeatedly arity #(gensym "argument")))]
                                     (cons {:op :fn :arity arity :rest? false :params ps
                                            :body {:op :prim :name primitive
                                                   :args (mapv #(hash-map :op :local :name %) ps)}}
                                           (rest args))) args)]
                        {:op :prim :name n :args (vec args)})) t)))]
      {:term (go term) :changes @changes :guards @guards})))

(defn collection-guards
  "Reduce/mapv may hand their callback to a custom reducing protocol.
  Admit owned public traversal results or exact vector entry arguments;
  everything else declines before execution. No mid-body replay."
  [term]
  (let [params (zipmap (:params term) (range)) guards (atom #{})]
    (letfn [(safe? [t known]
              (or (and (= :local (:op t)) (contains? known (:name t)))
                  (and (= :quote (:op t))
                       (or (nil? (:datum t))
                           (contains? #{clojure.lang.PersistentVector clojure.lang.PersistentList
                                        clojure.lang.PersistentList$EmptyList}
                                      (class (:datum t)))))
                  (and (= :prim (:op t))
                       (contains? '#{vector vec list map filter mapv range} (:name t)))))
            (go [t known]
              (when (and (= :prim (:op t)) (contains? '#{reduce mapv} (:name t)))
                (let [coll (last (:args t))]
                  (when-not (safe? coll known)
                    (if-let [i (when (= :local (:op coll)) (get params (:name coll)))]
                      (swap! guards conj [:arg i :persistent-vector])
                      (throw (ex-info "compile: HOF collection traversal is not known"
                                      {:klara/error :compile :op :prim}))))))
              (if (= :let (:op t))
                (do (go (:init t) known)
                    (go (:body t) (cond-> known (safe? (:init t) known) (conj (:name t)))))
                (ir/map-children #(do (go % known) %) t)))]
      (go term #{})
      @guards)))
