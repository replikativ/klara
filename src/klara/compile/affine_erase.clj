(ns klara.compile.affine-erase
  "Derivation-checked erasure and a small JVM representation emitter.
  Kept separate from numeric compilation. No checks on external tokens
  are erased: only locally allocated, nonescaping places are accepted."
  (:require [klara.affine :as affine] [klara.core :as c]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as w]))

(defn- node-at [t path] (get-in t path))

(defn- increment-index
  "The only in-place callback currently licensed: (fn [v]
  (assoc v literal-index (inc (nth v literal-index))))."
  [f length]
  (let [b (:body f) [v i rhs] (:args b) [get-v get-i] (:args (first (:args rhs)))
        index (:datum i)]
    (when (and (= :fn (:op f)) (= 1 (:arity f)) (not (:rest? f))
               (= :prim (:op b)) (= 'assoc (:name b)) (= 3 (count (:args b)))
               (= (c/local 0) v) (= :quote (:op i))
               (integer? index) (<= 0 index) (< index length)
               (= :prim (:op rhs)) (= 'inc (:name rhs)) (= 1 (count (:args rhs)))
               (= :prim (:op (first (:args rhs)))) (= 'nth (:name (first (:args rhs))))
               (= 2 (count (:args (first (:args rhs)))))
               (= (c/local 0) get-v) (= i get-i))
      index)))

(defn- representations [term derivation]
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
                                           (some? (increment-index (second (:args t)) (count v)))))) uses))]
        [path {:rep :long-vector :length (count v)}]))))

(defn erase
  "Verify a derivation, then emit check-free Clojure forms. :in-place? false
  selects the functional boxed representation for differential testing.
  This pass cannot be enabled by metadata alone. Returns forms and facts."
  ([term derivation] (erase term derivation {}))
  ([term derivation {:keys [in-place? unbox-parameters?] :or {in-place? true}}]
   (affine/verify! term derivation)
   (let [reps (if in-place? (representations term derivation) {})]
     (letfn [(unsupported [t] (throw (ex-info "affine erasure: unsupported emission shape"
                                                          {:klara/error :compile :term t})))
             (emit [t env p tail?]
               (let [go #(emit %1 env (conj p %2) false)
                     expr #(:form (go %1 %2))
                     local #(nth env (- (count env) 1 %))]
                 (case (:op t)
                   :quote {:form (list 'quote (:datum t))}
                   :local (local (:index t))
                   :prim {:form (list* (symbol "clojure.core" (name (:name t)))
                                      (map-indexed (fn [i a] (:form (emit a env (conj p :args i) false))) (:args t)))}
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
                             b (:form (emit (:body t) (into env (map #(hash-map :form %) ps)) (conj p :body) true))]
                         {:form (list 'fn raw
                                      (if (= ps raw) b
                                        (list 'let (vec (mapcat (fn [p r] [p (list 'long r)]) ps raw)) b)))})
                   :letrec
                   (let [f (first (:inits t)) call (:body t)
                         ps (vec (repeatedly (:arity f) #(gensym "index")))
                         e (conj env {:loop true})]
                     (when-not (and (= :app (:op call)) (= (c/local 0) (:fn call))) (unsupported t))
                     {:form (list 'loop
                                  (vec (mapcat (fn [s i a] [s (:form (emit a e (conj p :body :args i) false))])
                                               ps (range) (:args call)))
                                  (:form (emit (:body f) (into e (map #(hash-map :form %) ps))
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
                           (let [i (increment-index (second args) (:length v))]
                             (when-not (some? i) (unsupported t))
                             (assoc v :form
                                    (list 'let [(with-meta s {:tag 'longs}) (:form v)]
                                          (list 'aset-long s i (list 'inc (list 'aget s i))) s)))
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
