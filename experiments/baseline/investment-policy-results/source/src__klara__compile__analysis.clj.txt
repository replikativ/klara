(ns klara.compile.analysis
  "Small shared transfer rules and conservative first-order summary expansion.
   Derivations are inspectable tested evidence, not kernel proofs. Unknown
   operations decline. Layout checking of the expanded caller is mandatory."
  (:require [clojure.set :as set]
            [klara.core :as c]
            [klara.compile.ir :as ir]))

(def version "analysis-1")
(def scalar-ops '#{+ - * inc dec < <= > >= = not= not zero? pos? neg?})

(defn scalar-result [op types]
  (let [n (count types) longs? (every? #{:long :int} types)
        scalar? (every? #{:long :int :boolean} types)]
    (case op
      (+ *) (when longs? (if (= 1 n) (first types) :long))
      - (when (and longs? (pos? n)) :long)
      (inc dec) (when (and longs? (= 1 n)) :long)
      (< <= > >=) (when (and longs? (pos? n)) :boolean)
      (= not=) (when (and scalar? (pos? n)) :boolean)
      not (when (and scalar? (= 1 n)) :boolean)
      (zero? pos? neg?) (when (and longs? (= 1 n)) :boolean)
      nil)))

(defn expression-type [t env]
  (case (:op t)
    :quote (cond (instance? Long (:datum t)) :long
                 (boolean? (:datum t)) :boolean)
    :local (get env (:name t))
    :prim (let [types (mapv #(expression-type % env) (:args t))]
            (case (:name t)
              nth (when (and (= 2 (count types)) (= :long-vector (first types)) (#{:long :int} (second types))) :long)
              count (when (= types [:long-vector]) :int)
              (scalar-result (:name t) types)))
    nil))

(defn decline! [check message & [data]]
  (throw (ex-info message (merge {:reason :unsupported-region :check check} data))))

(defn indexed
  "Restore indices from fresh named core, rejecting escaped local names."
  ([t] (indexed t []))
  ([t env]
   (case (:op t)
     :local (let [i (.lastIndexOf ^java.util.List env (:name t))]
              (when (neg? i) (decline! :scope "unbound analysis local"))
              (c/local (- (count env) i 1)))
     :fn (c/lam (:arity t) (:rest? t) (indexed (:body t) (into env (:params t))))
     :let (c/let1 (indexed (:init t) env) (indexed (:body t) (conj env (:name t))))
     :letrec (let [e (into env (:names t))]
               (c/letrec (mapv #(indexed % e) (:inits t)) (indexed (:body t) e)))
     (ir/map-children #(indexed % env) t))))

(defn summarize
  "Summarize a closed first-order pure helper without running it. References
   in returned containers count as retention even without a write. assoc/nth
   require the caller to establish inert Long-vector layouts; summaries are
   not independently executable or permission to skip caller checking."
  [source]
  (try (c/assert-wf! source)
       (catch Exception _ (decline! :helper-capture "helper must be closed")))
  (when-not (and (= :fn (:op source)) (not (:rest? source))
                 (empty? (c/free-globals source)))
    (decline! :helper-contract "expected closed fixed-arity helper"))
  (let [named (ir/named source) requirements (atom {})]
    (letfn [(require-layout! [value expected]
              (let [layout (:layout value)]
                (cond
                  (and (vector? layout) (= :parameter (first layout)))
                  (let [i (second layout) old (get @requirements i)]
                    (when (and old (not= old expected))
                      (decline! :helper-layout "inconsistent helper argument requirements"))
                    (swap! requirements assoc i expected))
                  (and (= layout :vector) (= expected :long-vector))
                  (if (contains? value :elements)
                    (doseq [v (:elements value)] (require-layout! v :long))
                    (decline! :helper-layout "vector element layouts are unknown"))
                  (= layout expected) nil
                  :else (decline! :helper-layout "helper intermediate has incompatible layout"))))
            (value [layout refs] {:layout layout :references refs})
            (join-values [a b]
              (let [layout (if (= (:layout a) (:layout b)) (:layout a) :unknown)
                    result (value layout (set/union (:references a) (:references b)))]
                (if (= :vector layout)
                  (if (and (contains? a :elements) (contains? b :elements)
                           (= (count (:elements a)) (count (:elements b))))
                    (assoc result :elements (mapv join-values (:elements a) (:elements b)))
                    (assoc result :layout :unknown)) result)))
            (references [t env]
              (case (:op t)
                :quote (let [x (:datum t)]
                         (cond (instance? Long x) (value :long #{})
                               (boolean? x) (value :boolean #{})
                               (nil? x) (value :nil #{})
                               (and (= clojure.lang.PersistentVector (class x))
                                    (every? #(instance? Long %) x))
                               (assoc (value :vector #{}) :elements (mapv (fn [_] (value :long #{})) x))
                               :else (decline! :helper-constant "unsupported helper constant")))
                :local (or (get env (:name t)) (decline! :scope "unbound helper local"))
                :let (let [a (references (:init t) env)]
                       (references (:body t) (assoc env (:name t) a)))
                :if (do (references (:test t) env)
                        (join-values (references (:then t) env) (references (:else t) env)))
                :prim (let [args (:args t) values (mapv #(references % env) args)]
                        (cond
                          (contains? scalar-ops (:name t))
                          (let [types (mapv (fn [v]
                                              (if (vector? (:layout v))
                                                (do (require-layout! v :long) :long)
                                                (:layout v))) values)
                                result (scalar-result (:name t) types)]
                            (when-not result (decline! :helper-layout "invalid scalar helper operation"))
                            (value result #{}))
                          (= 'vector (:name t))
                          (assoc (value :vector (apply set/union #{} (map :references values)))
                                 :elements values)
                          (= 'nth (:name t))
                          (do (when-not (= 2 (count args))
                                (decline! :helper-arity "nth helper arity"))
                              (require-layout! (second values) :long)
                              (let [base (first values) index (:datum (second args))]
                                (if (and (= :vector (:layout base)) (instance? Long index)
                                         (<= 0 index) (< index (count (:elements base))))
                                  (nth (:elements base) index)
                                  (do (require-layout! base :long-vector) (value :long #{})))))
                          (= 'assoc (:name t))
                          (do (when-not (= 3 (count args))
                                (decline! :helper-arity "assoc helper arity"))
                              (require-layout! (first values) :long-vector)
                              (require-layout! (second values) :long)
                              (require-layout! (nth values 2) :long)
                              (value :long-vector #{}))
                          :else (decline! :helper-operation "unsupported helper primitive"
                                         {:primitive (:name t)})))
                (decline! :helper-effect "helper has unknown calls, effects or control"
                          {:op (:op t)})))]
      (let [result (references (:body named)
                               (zipmap (:params named)
                                       (map #(value [:parameter %] #{%}) (range (:arity source)))))]
        {:version version :source source :source-id (c/code-id source)
         :arity (:arity source) :result result
         :retained-arguments (:references result)
         :requirements (set (map (fn [[i layout]] [layout i]) @requirements))
         :effects #{:possible-checked-failure}
         :validation :reanalyze-expanded-caller}))))

(defn normalize
  "Eliminate local aliases and expand checked closed helper calls in order.
   helpers maps mandatory prefix world names to {:source core :value-id id}.
   A use-demand pass conservatively treats every used binding as observable.
   Retaining helper results in demanded positions decline before loop lowering.
   The returned term MUST pass the ownership/layout conversion afterwards."
  ([source] (normalize source {}))
  ([source helpers]
   (c/assert-wf! source)
   (let [rules (atom []) used (atom {}) steps (atom 0)
         summaries (update-vals helpers #(assoc % :summary (summarize (:source %))))]
     (letfn [(go [t env path demanded?]
               (when (> (swap! steps inc) 10000)
                 (decline! :analysis-budget "summary expansion budget exhausted"))
               (case (:op t)
                 :local (let [a (get env (:name t))]
                          (if (= :local (:op a)) a t))
                 :let
                 (let [init (:init t) name (:name t)
                       demand? (pos? (ir/uses (:body t) name))]
                   (cond
                     (= :local (:op init))
                     (let [v (get env (:name init) init)]
                       (swap! rules conj {:rule :alias :at path})
                       (go (:body t) (assoc env name v) (conj path :body) demanded?))
                     (= :fn (:op init))
                     (let [summary (summarize (indexed init))]
                       (swap! used assoc (:source-id summary) summary)
                       (go (:body t) (assoc env name {:summary summary}) (conj path :body) demanded?))
                     (= :resolve (:op init))
                     (if-let [h (get summaries (:id init))]
                       (if (contains? (set (:read-paths h)) path)
                       (do (swap! used assoc (:source-id (:summary h)) (:summary h))
                           (go (:body t) (assoc env name {:summary (:summary h)})
                               (conj path :body) demanded?))
                       (decline! :late-world-read "helper read is not in the mandatory entry prefix"))
                       (decline! :world-summary "missing mandatory helper summary"))
                     :else
                     (assoc t :init (go init env (conj path :init) demand?)
                              :body (go (:body t) env (conj path :body) demanded?))))
                 :app
                 (let [target (:fn t) h (when (= :local (:op target)) (get env (:name target)))
                       args (mapv #(go %1 env (conj path :args %2) true) (:args t) (range))]
                   (if-let [summary (:summary h)]
                     (do
                       (when-not (= (:arity summary) (count args))
                         (decline! :helper-arity "helper call arity differs"))
                       (when (and demanded? (seq (:retained-arguments summary)))
                         (decline! :retained-version "helper result retains an argument"
                                   {:summary-id (:source-id summary)
                                    :arguments (:retained-arguments summary)}))
                       (swap! rules conj {:rule :summary-call :at path :summary-id (:source-id summary)})
                       (let [f (ir/named (:source summary))]
                         ;; Bind in source order, never duplicate a computed argument.
                         (go (reduce (fn [b [p a]] {:op :let :name p :init a :body b})
                                     (:body f) (reverse (map vector (:params f) args)))
                             env (conj path :expanded) demanded?)))
                     (assoc t :fn (go target env (conj path :fn) true) :args args)))
                 :if (assoc t :test (go (:test t) env (conj path :test) true)
                              :then (go (:then t) env (conj path :then) demanded?)
                              :else (go (:else t) env (conj path :else) demanded?))
                 :fn (assoc t :body (go (:body t) env (conj path :body) true))
                 :letrec (assoc t :inits (mapv #(go %1 env (conj path :inits %2) true)
                                               (:inits t) (range))
                                  :body (go (:body t) env (conj path :body) demanded?))
                 :prim (assoc t :args (mapv #(go %1 env (conj path :args %2) demanded?)
                                            (:args t) (range)))
                 :resolve (decline! :late-world-read "only mandatory prefix helper reads are admitted")
                 :quote t
                 (decline! :effect "unsupported effect or control in analyzed region" {:op (:op t)})))]
       (let [term (indexed (go (ir/named source) {} [] true))]
         {:version version :source-id (c/code-id source) :term term
          :normalized-id (c/code-id term) :rules @rules :summaries @used})))))
