(ns klara.compile.affine-erase
  "Derivation-checked erasure and a small JVM representation emitter.
  Kept separate from numeric compilation. No checks on external tokens
  are erased: only locally allocated, nonescaping places are accepted."
  (:require [klara.affine :as affine] [klara.core :as c]
            [klara.compile.updates :as updates]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as w]))

(defn- node-at [t path] (get-in t path))

(defn- representations [term derivation plans]
  ;; No transfer representation is claimed yet. Borrow reads make persistent
  ;; snapshots, so they cannot observe subsequent array writes.
  (if (some #(= :own/move (:rule %)) (:rules derivation)) {}
    (into {}
      (for [{:keys [path rule]} (:rules derivation)
            :when (= rule :own/alloc)
            :let [v (:datum (first (:args (node-at term path))))
                  uses (filter #(and (= :permission (:rule %)) (= path (:resource %))) (:rules derivation))]
            :when (and (vector? v) (seq v) (every? #(instance? Long %) v)
                       (every? #(or (not= :own/update (:operation %))
                                    (let [t (node-at term (:path %))]
                                      (and (= 2 (count (:args t)))
                                           (contains? plans (:path %))))) uses))]
        [path {:rep :long-vector :length (count v)}]))))

(defn fallback
  "Opaque inputs retain T0's dynamic checks and effect admission."
  [term args]
  (ev/call-value (ev/run term) args))

(defn erase
  "Verify a derivation, then emit check-free Clojure forms. :in-place? false
  selects the functional boxed representation for differential testing.
  :admitted-parameters? skips redundant entry checks only for a caller whose
  stage guards establish :parameter-layouts. This is a trusted compiler option.
  Returns forms and facts; the ownership derivation is always rechecked."
  ([term derivation] (erase term derivation {}))
  ([term derivation {:keys [in-place? unbox-parameters? parameter-layouts admitted-parameters?] :or {in-place? true}}]
   (affine/verify! term derivation)
   (let [layouts (if unbox-parameters?
                   (or parameter-layouts (vec (repeat (or (:arity term) 0) :long)))
                   (vec (repeat (or (:arity term) 0) nil)))
         plans (updates/plans term layouts)
         reps (if in-place? (representations term derivation plans) {})]
     (letfn [(unsupported [t] (throw (ex-info "affine erasure: unsupported emission shape"
                                                          {:klara/error :compile :term t})))
             (emit [t env p tail?]
               (let [go #(emit %1 env (conj p %2) false)
                     expr #(:form (go %1 %2))
                     local #(nth env (- (count env) 1 %))]
                 (case (:op t)
                   :quote {:form (list 'quote (:datum t)) :layout (updates/expression-type t [])}
                   :local (local (:index t))
                   :prim (let [args (mapv (fn [i a] (emit a env (conj p :args i) false)) (range) (:args t))
                               ty (updates/expression-type t (mapv :layout env))
                               form (list* (symbol "clojure.core" (name (:name t))) (map :form args))]
                           {:form (if (and (= ty :long) (#{'nth 'count} (:name t))) (list 'long form) form)
                            :layout ty})
                   :let (let [v (go (:init t) :init) s (gensym "place")
                              body (emit (:body t) (conj env (assoc v :form s)) (conj p :body) tail?)]
                          (assoc body :form (list 'let [s (:form v)] (:form body))))
                   :if (let [a (emit (:then t) env (conj p :then) tail?)
                             b (emit (:else t) env (conj p :else) tail?)]
                         (assoc (if (= (dissoc a :form) (dissoc b :form)) a {})
                                :form (list 'if (expr (:test t) :test) (:form a) (:form b))))
                   :fn (let [ps (vec (repeatedly (:arity t) #(gensym "arg")))
                             raw (if (and unbox-parameters? (empty? env))
                                   (vec (repeatedly (:arity t) #(gensym "raw"))) ps)
                             b (:form (emit (:body t) (into env (map (fn [p ty] {:form p :layout ty}) ps
                                                                     (if (empty? env) layouts (repeat nil)))) (conj p :body) true))]
                         {:form (list 'fn raw
                                      (list 'if
                                            (if (and (empty? env) (not admitted-parameters?))
                                              (list 'and (list 'every? 'klara.affine/value? raw)
                                                    (if unbox-parameters?
                                                      (list* 'and (map (fn [r ty] (if (= ty :long-vector)
                                                                                  (list 'klara.stage/argument-holds? :long-vector r)
                                                                                  (list 'instance? 'Long r))) raw layouts))
                                                      true)) true)
                                            (if (= ps raw) b
                                              (list 'let (vec (mapcat (fn [p r ty] [p (if (= ty :long-vector) r (list 'long r))]) ps raw layouts)) b))
                                            (list 'klara.compile.affine-erase/fallback (list 'quote t) raw)))})
                   :letrec
                   (let [f (first (:inits t)) call (:body t)
                         ps (vec (repeatedly (:arity f) #(gensym "index")))
                         e (conj env {:loop true})]
                     (when-not (and (= :app (:op call)) (= (c/local 0) (:fn call))) (unsupported t))
                     {:form (list 'loop
                                  (vec (mapcat (fn [s i a] [s (:form (emit a e (conj p :body :args i) false))])
                                               ps (range) (:args call)))
                                  (:form (emit (:body f) (into e (map (fn [s a] {:form s :layout (updates/expression-type a (mapv :layout e))}) ps (:args call)))
                                               (conj p :inits 0 :body) true)))})
                   :app (do (when-not (and (= :local (get-in t [:fn :op]))
                                          (:loop (local (get-in t [:fn :index]))) tail?) (unsupported t))
                            {:form (list* 'recur (map-indexed (fn [i a] (:form (emit a env (conj p :args i) false))) (:args t)))})
                   :perform
                   (let [op (:name t) args (:args t)
                         a (fn [i] (emit (nth args i) env (conj p :args i) false))]
                     (case op
                       :host/var {:form (:datum (first args))}
                       :own/alloc (let [rep (reps p) v (:form (a 0))]
                                    (assoc (or rep {}) :form
                                           (if rep (list 'long-array v) (list 'object-array [v]))))
                       :own/read (let [v (a 0)] {:form (if (:rep v) (list 'vec (:form v)) (list 'aget (:form v) 0))})
                       :own/freeze (let [v (a 0)] {:form (if (:rep v) (list 'vec (:form v)) (list 'aget (:form v) 0))})
                       :own/drop {:form (list 'do (:form (a 0)) nil)}
                       :own/move (a 0)
                       :own/borrow (let [v (a 0) s (gensym "loan") f (second args)
                                         b (emit (:body f) (conj env (assoc v :form s)) (conj p :args 1 :body) tail?)]
                                     (assoc b :form (list 'let [s (:form v)] (:form b))))
                       :own/update
                       (let [v (a 0) s (gensym "buffer")]
                         (if (:rep v)
                           (let [plan (plans p)
                                 temps (vec (repeatedly (count (:writes plan)) #(gensym "rhs")))
                                 callback-env (conj env {:form s})]
                             (when-not plan (unsupported t))
                             (letfn [(rhs [t env depth]
                                       (let [child #(rhs % env depth)]
                                         (case (:op t)
                                           :local (:form (nth env (- (count env) 1 (:index t))))
                                           :quote (list 'quote (:datum t))
                                           :let (let [init (child (:init t)) name (gensym "scalar")]
                                                  (list 'let [name init]
                                                        (rhs (:body t) (conj env {:form name}) (inc depth))))
                                           :prim (let [as (:args t)]
                                                   (case (:name t)
                                                     nth (if (= (c/local depth) (first as))
                                                           (list 'aget s (:datum (second as)))
                                                           (list 'long (list 'clojure.core/nth (child (first as)) (child (second as)))))
                                                     count (if (= (c/local depth) (first as)) (:length v)
                                                             (list 'long (list 'clojure.core/count (child (first as)))))
                                                     (list* (symbol "clojure.core" (name (:name t))) (map child as)))))))]
                               (assoc v :form
                                      (list 'let (into [(with-meta s {:tag 'longs}) (:form v)]
                                                       (mapcat (fn [tmp write] [tmp (rhs (:rhs write) callback-env 0)]) temps (:writes plan)))
                                            (cons 'do (concat (map (fn [tmp write] (list 'aset s (:index write) tmp)) temps (:writes plan)) [s]))))))
                           (let [f (gensym "update") more (vec (repeatedly (- (count args) 2) #(gensym "argument")))]
                             (assoc v :form
                                    (list 'let (into [s (:form v) f (:form (a 1))]
                                                     (mapcat (fn [s i] [s (:form (a i))]) more (range 2 (count args))))
                                          (list 'aset s 0 (list* f (list 'aget s 0) more)) s)))))
                       (unsupported t)))
                   (unsupported t))))]
       {:form (:form (emit term [] [] true)) :derivation derivation
        :representations reps :checks-erased (count (filter #(= :permission (:rule %)) (:rules derivation)))}))))

(stage/register-checker! :klara.affine/tested
  (fn [exe]
    (when-not (and (= (:code-id exe) (c/code-id (:generic exe)))
                   (= affine/version (get-in exe [:certificate :checker-version]))
                   (= (:derivation exe) (affine/check (:generic exe)))
                   (= (get-in exe [:certificate :derivation]) (stage/digest (:derivation exe)))
                   (fn? (:run exe)))
      :invalid-affine-derivation)))

(defn wrap-compiler
  "One-line compile/core hook. Unsupported/inferred regions use the ordinary
  compiler. Owned boundary contracts are never silently optimized."
  [ordinary]
  (fn compile-affine
    ([world sym] (compile-affine world sym {}))
    ([world sym opts]
     (let [basis (if (instance? klara.world.World world) (w/snapshot world) world)
           e (w/entry* basis sym) f (:value e)
           source (when (ev/closure? f) (ev/closure-term f))
           owned? (some #(and (= :perform (:op %)) (= "own" (namespace (:name %))))
                        (when source (tree-seq #(seq (c/children %)) c/children source)))
           d (when (and owned? (empty? (ev/closure-locals f)) (not (w/pending? basis e))) (affine/check source))]
       (if-not d (ordinary world sym opts)
         (let [start (System/nanoTime) erased (erase source d)
               fast (erase source d {:unbox-parameters? true})
               generic-run (eval (:form erased)) fast-run (eval (:form fast))
               guards #{[:captures []] [:statics []] [:unhandled #{:exn/raise}]}
               cert (-> (stage/certify (c/code-id source) guards :klara.affine/tested
                                      {:suite "test/klara/affine_test.clj" :obligation :AF3})
                        (assoc :kind :tested :checker-version affine/version :derivation (stage/digest d))
                        (dissoc :digest))]
           (merge erased
             {:run (fn [& args]
                     (if (not= (:arity source) (count args)) ev/deopt
                       (apply (if (every? #(instance? Long %) args) fast-run generic-run) args)))
              :form (:form fast) :generic source :code-id (c/code-id source) :name sym :guards guards
              :certificate (assoc cert :digest (stage/digest cert))
              :compile-ms (/ (- (System/nanoTime) start) 1e6)
              :allocations-removed 0 :ir source
              :pass-log [{:pass :affine-erase :checks (:checks-erased erased)}
                         {:pass :affine-represent :buffers (count (:representations erased))}
                         {:pass :emit :backend :clojure}]})))))))
