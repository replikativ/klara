(ns klara.compile.infer-affine
  "Experimental functional accumulator -> private owned region conversion.
   Alias/retention normalization precedes conservative loop checking;
   profiling is only a request to prepare.
   All three bridges (conversion, erasure, representation) are tested, not proved."
  (:require [klara.affine :as affine]
            [klara.authority :as authority]
            [klara.code :as code]
            [klara.compile.analysis :as analysis]
            [klara.compile.affine-erase :as erase]
            [klara.compile.ir :as ir]
            [klara.compile.staged :as staged]
            [klara.compile.updates :as updates]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(def version "inferred-accumulator-4")
(def ^:private scalar-ops analysis/scalar-ops)
(def ^:private reference-prims c/prims)
(def ^:private reference-roots
  (into #{[:host-root 'klara.core/prims reference-prims]
          [:host-root 'klara.affine/value? @#'affine/value?]}
        (for [s (into scalar-ops '#{assoc nth count long-array vec long every? aset aget})]
          [:host-root (symbol "clojure.core" (name s)) @(ns-resolve 'clojure.core s)])))

(defn- entry-guards [layouts summaries]
  (into (into reference-roots #{[:captures []] [:statics []] [:arity (count layouts)]
                                [:unhandled #{:exn/raise}]})
        (concat (map-indexed (fn [i layout] [:arg i layout]) layouts)
                (for [[sym h] summaries] [:world sym (:value-id h)]))))

(defn- fail [message]
  (throw (ex-info message {:reason :unsupported-region})))
(defn- local [s] {:op :local :name s})
(defn- let-node [s init body] {:op :let :name s :init init :body body})
(defn- own [op & args] (apply c/perform nil op args))

(def ^:private indexed analysis/indexed)
(def ^:private scalar-type analysis/expression-type)

(defn infer
  "Convert one direct tail loop with one literal Long-vector accumulator.
   Other loop variables are scalar. Accumulator uses must be scalar
   snapshot assoc updates on backedges or the terminal result. Harmless aliases and
   closed summarized helpers normalize first; retained histories, unknown calls,
   effects and input buffers decline. Returns inspectable
   original/owned core and separately checked ownership derivation."
  ([source] (infer source {}))
  ([source summary-inputs] (infer source summary-inputs {}))
  ([source summary-inputs {:keys [parameter-layouts]}]
  (c/assert-wf! source)
  (when-not (and (= :fn (:op source)) (not (:rest? source)) (<= (:arity source) 4))
    (fail "expected a fixed function with at most four layout-admitted arguments"))
  (let [layouts (or parameter-layouts (vec (repeat (:arity source) :long)))
        _ (when-not (and (= (count layouts) (:arity source)) (every? #{:long :long-vector} layouts))
            (fail "unsupported parameter layouts"))
        analyzed (analysis/normalize source summary-inputs)
        named (ir/named (:term analyzed)) facts (atom [])]
    (letfn [(convert-loop [t constants allowed]
              (let [f (first (:inits t)) call (:body t) self (first (:names t))
                    args (:args call)
                    literal #(case (:op %) :quote (:datum %) :local (get constants (:name %)) nil)
                    vectors (keep-indexed (fn [i a] (when (vector? (literal a)) i)) args)]
                (when-not (and (= 1 (count (:inits t))) (= :fn (:op f)) (not (:rest? f))
                               (= :app (:op call)) (= (local self) (:fn call))
                               (= (:arity f) (count args)) (= 1 (count vectors)))
                  (fail "expected one directly entered loop and one constant vector accumulator"))
                (let [position (first vectors) initial (literal (nth args position))
                      acc (nth (:params f) position) cell (gensym "owned")
                      scalar-params (vec (concat (take position (:params f)) (drop (inc position) (:params f))))
                      scalars (merge allowed (zipmap scalar-params (repeat :long)))
                      without-acc #(vec (concat (take position %) (drop (inc position) %)))
                      updates (atom [])]
                  (when-not (and (= clojure.lang.PersistentVector (class initial))
                                 (seq initial) (every? #(instance? Long %) initial)
                                 (every? #(= :long (scalar-type % allowed)) (without-acc args)))
                    (fail "expected inert Long vector and scalar loop initializers"))
                  (letfn [(tail [b allowed]
                            (case (:op b)
                              :if (do (when-not (#{:long :int :boolean} (scalar-type (:test b) allowed)) (fail "test observes accumulator or effect"))
                                      (assoc b :then (tail (:then b) allowed) :else (tail (:else b) allowed)))
                              :let (let [type (scalar-type (:init b) allowed)]
                                     (when-not (#{:long :int :boolean} type) (fail "binding retains/observes accumulator or effect"))
                                     (assoc b :body (tail (:body b) (assoc allowed (:name b) type))))
                              :local (if (= (local acc) b) (c/quote* nil)
                                         (fail "loop must return its accumulator"))
                              :app
                              (let [as (:args b) update (get as position)
                                    outer (vec (sort (keys allowed)))
                                    v (gensym "value")
                                    callback {:op :fn :arity 1 :rest? false :params [v]
                                              :body (ir/substitute update {acc (local v)})}
                                    plan (updates/plan (analysis/indexed callback outer) (count initial) (mapv allowed outer))
                                    temps (vec (repeatedly (count as) #(gensym "next")))]
                                (when-not (and (= (local self) (:fn b)) (= (:arity f) (count as))
                                               (some? plan) (every? #(= :long (scalar-type % allowed)) (without-acc as)))
                                  (fail "backedge escapes accumulator or has unsupported update"))
                                (swap! updates into (map :index (:writes plan)))
                                ;; Let every recur argument in source order before assignment.
                                ;; In particular, exceptions before/after the update stay ordered.
                                (reduce (fn [body [i s a]]
                                          (let-node s
                                            (if (= i position)
                                              (own :own/update (local cell)
                                                   callback) a)
                                            body))
                                        (assoc b :args (mapv local (without-acc temps)))
                                        (reverse (map vector (range) temps as))))
                              (fail "unsupported accumulator tail/effect")))]
                    (let [body (tail (:body f) scalars)
                          loop (assoc t :inits [(assoc f :params scalar-params :arity (count scalar-params) :body body)]
                                        :body (assoc call :args (without-acc args)))
                          result (gensym "done")]
                      (when (empty? @updates) (fail "no accumulator updates found"))
                      (swap! facts conj {:rule :private-copy :initial initial :length (count initial)
                                         :accumulator-position position :updates @updates
                                         :escape-policy :terminal-result-only
                                         :argument-order :left-to-right})
                      (let-node cell (own :own/alloc (c/quote* initial))
                                (let-node result loop (own :own/freeze (local cell)))))))))
            (prefix [t constants allowed]
              (case (:op t)
                :let (let [init (:init t)
                           value (case (:op init) :quote (:datum init) :local (get constants (:name init)) nil)]
                       (when-not (or (scalar-type init allowed)
                                     (and (= clojure.lang.PersistentVector (class value))
                                          (every? #(instance? Long %) value)))
                         (fail "only scalar or literal-vector prefix bindings are supported"))
                       (assoc t :body (prefix (:body t) (assoc constants (:name t) value)
                                             (if (vector? value) allowed
                                               (assoc allowed (:name t) (scalar-type init allowed))))))
                :letrec (convert-loop t constants allowed)
                (fail "expected a functional accumulator loop")))]
      (let [owned (indexed (assoc named :body (prefix (:body named) {} (zipmap (:params named) layouts))))
            derivation (affine/check owned :declared)]
        {:version version :parameter-layouts layouts :source-id (c/code-id source) :owned owned
         :analysis analyzed :derivation derivation :facts @facts
         :reference-protocol :private-store-finally})))))

(defn execute-owned
  "Reference execution for the inferred private owned IR. Its store is local
   to the region, contains no caller rights, and is settled on every exit.
   Bare ev/run of the owned term is not this region execution protocol."
  [inferred args]
  (affine/verify! (:owned inferred) (:derivation inferred))
  (when-not (every? #(stage/guard-holds? % {}) reference-roots)
    (fail "changed reference primitives"))
  (binding [authority/*store* (authority/new-store)
            ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
            ev/*outer-k* [] ev/*fiber* nil]
    (try
      (ev/call-value (ev/run (:owned inferred) {:basis w/empty-root}) args)
      (finally
        ;; The checked fragment has only local full-share cells, no loans,
        ;; transfers or other authority kinds. Never settle caller tokens.
        (doseq [[id state] (:tokens @authority/*store*)
                :when (and (= :owned (:kind state)) (= :open (:status state)))]
          (authority/op! :own/drop [(klara.authority.Auth. id :owned)] []))))))

(defn- entry-summaries [source root]
  (loop [body (:body source) path [:body] inputs {}]
    (if (and (= :let (:op body)) (= :resolve (get-in body [:init :op])))
      (let [sym (get-in body [:init :id]) e (w/entry* root sym) f (:value e)]
        (when-not (and (= :def (:kind e)) (not (w/pending? root e))
                       (ev/closure? f) (empty? (ev/closure-locals f)))
          (analysis/decline! :world-summary "entry helper must be a current closed function"))
        (recur (:body body) (conj path :body)
               (update inputs sym
                 (fn [old] {:source (ev/closure-term f) :value-id (:value-id e)
                            :read-paths (conj (:read-paths old []) path)}))))
      inputs)))

(defn- definition-reads [inputs]
  (mapv (fn [[sym h _]] [:value sym (:value-id h)])
        (sort-by (comp count last)
                 (for [[sym h] inputs path (:read-paths h)] [sym h path]))))

(stage/register-checker!
 :klara.compile/inferred-affine
 (fn [exe]
   (try
     (let [inputs (:summary-inputs exe) inferred (infer (:generic exe) inputs {:parameter-layouts (:parameter-layouts exe)})]
       (when-not (and (= :tested (get-in exe [:certificate :kind]))
                      (= version (get-in exe [:certificate :checker-version]))
                      (= (:code-id exe) (:source-id inferred))
                      (= (:guards exe) (entry-guards (:parameter-layouts inferred) inputs))
                      (= (:definition-reads exe) (definition-reads inputs))
                      (= inferred (:inference exe))
                      (if (= 1 (:arity (:generic exe))) (fn? (:invoke1 exe)) (nil? (:invoke1 exe)))
                      (= (stage/digest inferred) (get-in exe [:certificate :inference-digest]))
                      (fn? (:run exe)))
         :invalid-inferred-affine))
     (catch Exception _ :invalid-inferred-affine))))

(defn prepare
  "Same isolated preparation and Prepared/install lifecycle as S23. The seed
   analyzer is trusted host code; no source computation runs during preparation."
  ([root source] (prepare root source {}))
  ([root source opts]
  (let [start (System/nanoTime)]
    (when-not (and (code/code? source) (code/closed? source)) (fail "requires closed code"))
    (when-not (every? #(stage/guard-holds? % {}) reference-roots) (fail "changed reference primitives"))
    (binding [authority/*store* (authority/new-store)
              ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
              ev/*outer-k* [] ev/*fiber* nil w/*reads* nil]
      (let [generic (code/s->core (code/code-term source))
            inputs (entry-summaries generic root)
            reads (definition-reads inputs)
            analysis-start (System/nanoTime)
            inferred (infer generic inputs opts)
            analysis-ms (/ (- (System/nanoTime) analysis-start) 1e6)
            erase-start (System/nanoTime)
            erased (erase/erase (:owned inferred) (:derivation inferred) {:unbox-parameters? true :admitted-parameters? true :parameter-layouts (:parameter-layouts inferred)})
            erasure-ms (/ (- (System/nanoTime) erase-start) 1e6)
            emit-start (System/nanoTime)
            ;; Emission must not inherit a caller's arithmetic mode or symbol
            ;; resolution namespace. Those settings are not source assumptions.
            f (binding [*unchecked-math* false *ns* (the-ns 'klara.compile.affine-erase)]
                (eval (:form erased)))
            emission-ms (/ (- (System/nanoTime) emit-start) 1e6)
            cid (c/code-id generic) guards (entry-guards (:parameter-layouts inferred) inputs)
            cert (-> (stage/certify cid guards :klara.compile/inferred-affine
                                   {:suite "klara.infer-affine-test" :obligation :functional-to-owned})
                     (dissoc :digest)
                     (assoc :kind :tested :checker-version version :inference-digest (stage/digest inferred)))
            exe {:code-id cid :generic generic :guards guards :inference inferred
                 :summary-inputs inputs :parameter-layouts (:parameter-layouts inferred) :definition-reads reads
                 :run (fn [& args]
                        (doseq [read reads] (w/note-read! read))
                        (ev/invoke-boxed f args))
                 :invoke1 (when (= 1 (:arity generic))
                            (fn [x] (doseq [read reads] (w/note-read! read)) (f x)))
                 :certificate (assoc cert :digest (stage/digest cert))}
            info {:code-id cid :guards guards :inference inferred :form (:form erased)
                  :representations (:representations erased) :checks-erased (:checks-erased erased)
                  :analysis-ms analysis-ms :erasure-ms erasure-ms :emission-and-loading-ms emission-ms
                  :requires-entry-admission true
                  :compile-ms (/ (- (System/nanoTime) start) 1e6)}]
        (klara.compile.staged.Prepared. source exe info))))))

(ev/register-reference-handler!
 :stage/prepare-affine
 (fn [[source] env]
   (try (prepare (:basis env) source)
        (catch clojure.lang.ExceptionInfo e
          (if (= :unsupported-region (:reason (ex-data e)))
            {:status :declined :reason :unsupported-region :diagnostic (ex-message e)}
            (throw e))))))
