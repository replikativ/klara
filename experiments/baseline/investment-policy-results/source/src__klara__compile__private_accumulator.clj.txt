(ns klara.compile.private-accumulator
  "Terminal checked adapter: enclosed functional accumulator -> owned region.
   Only a pure boolean consumer can observe the final private vector. The
   ownership/conversion/JVM bridges are tested, not kernel-proved."
  (:require [klara.affine :as affine] [klara.compile.analysis :as analysis]
            [klara.compile.affine-erase :as erase] [klara.compile.budget :as budget]
            [klara.compile.edge :as edge] [klara.compile.infer-affine :as inference]
            [klara.compile.ir :as ir] [klara.compile.subject :as subject]
            [klara.compile.diagnostics :as diagnostics]
            [klara.core :as core] [klara.eval :as ev]))

(def ^:private seal (Object.))
(deftype Endpoint [source owned derivation accepted guards info authority])
(defmethod print-method Endpoint [_ out] (.write ^java.io.Writer out "#<private-accumulator-endpoint>"))
(defn endpoint? [x]
  (and (instance? Endpoint x) (identical? seal (.-authority ^Endpoint x))))
(defn- fail [check] (analysis/decline! check "private accumulator boundary rejected"))
(defn- bound! [b t]
  (loop [todo [[t 0]] n 0]
    (when-let [[node depth] (peek todo)]
      (budget/charge! b :work 1)
      (when (or (>= n 8192) (> depth 256)) (budget/exhausted! :owned-nodes))
      (recur (into (pop todo) (map #(vector % (inc depth))) (core/children node)) (inc n)))))

(defn- consumer-type [b t env result length]
  (budget/charge! b :work 1)
  (let [go #(consumer-type b % env result length)]
    (case (:op t)
      :quote (cond (instance? Long (:datum t)) :long (boolean? (:datum t)) :boolean)
      :local (when-not (= result (:name t)) (env (:name t)))
      :prim
      (let [as (:args t)]
        (case (:name t)
          nth (when (and (= 2 (count as)) (= {:op :local :name result} (first as))
                         (= :quote (:op (second as))) (instance? Long (:datum (second as)))
                         (<= 0 (:datum (second as))) (< (:datum (second as)) length)) :long)
          count (when (= as [{:op :local :name result}]) :int)
          (when (contains? analysis/scalar-ops (:name t))
            (analysis/scalar-result (:name t) (mapv go as)))))
      :let (when-let [ty (go (:init t))]
             (consumer-type b (:body t) (assoc env (:name t) ty) result length))
      :if (when (go (:test t))
            (let [a (go (:then t)) z (go (:else t))] (when (= a z) a)))
      nil)))

(defn- analyze [b source]
  (bound! b source)
  (when-not (and (= :fn (:op source)) (not (:rest? source)) (<= (:arity source) 4)
                 (= :let (get-in source [:body :op])))
    (fail :enclosed-loop))
  (let [body (:body source) layouts (vec (repeat (:arity source) :long))
        loop-source (analysis/indexed (assoc source :body (:init body)))
        inferred (diagnostics/phase :ownership-inference {:arity (:arity source)}
                   (inference/infer loop-source {} {:parameter-layouts layouts}))
        length (:length (first (:facts inferred)))
        _ (when-not (= :boolean (diagnostics/phase :consumer-admission {:length length}
                                 (consumer-type b (:body body) (zipmap (:params source) layouts)
                                                (:name body) length)))
            (fail :boolean-private-consumer))
        owned-named (ir/named (:owned inferred))
        consumer (ir/substitute (:body body)
                   (zipmap (:params source) (map #(hash-map :op :local :name %) (:params owned-named))))
        owned (analysis/indexed
                (assoc owned-named :body {:op :let :name (:name body)
                                         :init (:body owned-named) :body consumer}))
        _ (bound! b owned)
        derivation (diagnostics/phase :ownership-check {} (affine/check owned :declared))]
    {:source source :loop-source loop-source :inference inferred
     :owned owned :derivation derivation :guards (inference/parameter-guards layouts)
     :info {:kind :private-accumulator :result :boolean :temporary-escape :rejected
            :length length :parameter-layouts layouts :facts (:facts inferred)
            :boundary :checked-pure-consumer :semantic-bridge :tested
            :kernel-proof-attached? false}}))

(defn- reject! [check]
  (throw (ex-info "private analysis artifact rejected" {:reason :private-analysis :check check})))

(defn- literal-initial [source]
  ;; Independently decode the loop entry. Prefix values are never evaluated.
  ;; This intentionally covers the existing literal-only accumulator family.
  (loop [term (get-in source [:body :init]) constants {}]
    (case (:op term)
      :let (let [init (:init term)
                 value (case (:op init) :quote (:datum init) :local (constants (:name init)) nil)]
             (recur (:body term) (assoc constants (:name term) value)))
      :letrec (let [values (keep (fn [arg]
                                  (let [value (case (:op arg) :quote (:datum arg)
                                                :local (constants (:name arg)) nil)]
                                    (when (vector? value) value))) (get-in term [:body :args]))]
                (when (= 1 (count values)) (first values)))
      nil)))

(defn check-analysis!
  "Check a private candidate-local production artifact without rerunning infer.
   Checks the source/loop and consumer wiring, admission metadata and complete
   ownership derivation. Functional-to-owned inference remains a trusted/tested
   bridge, as before; this is not a universal conversion equivalence proof."
  [b source artifact]
  (let [{:keys [loop-source inference owned derivation guards info]} artifact
        body (:body source) layouts (vec (repeat (:arity source) :long))
        initial (literal-initial source)
        expected-loop (analysis/indexed (assoc source :body (:init body)))
        expected-consumer (get-in (analysis/indexed (assoc-in source [:body :init] (core/quote* nil))) [:body :body])]
    (budget/charge! b :work 1)
    (when-not (and (identical? source (:source artifact)) (= loop-source expected-loop)
                   (= (:source-id inference) (core/code-id loop-source)))
      (reject! :source-binding))
    (when-not (and (= :fn (:op owned)) (= (:arity source) (:arity owned)) (false? (:rest? owned))
                   (= :let (get-in owned [:body :op]))
                   (= (get-in inference [:owned :body]) (get-in owned [:body :init]))
                   (= expected-consumer (get-in owned [:body :body])))
      (reject! :owned-consumer-wiring))
    (when-not (and (= clojure.lang.PersistentVector (class initial)) (seq initial)
                   (every? #(instance? Long %) initial)
                   (= initial (:initial (first (:facts inference))))
                   (= (:length info) (count initial))
                   (= :boolean (consumer-type b (:body body) (zipmap (:params source) layouts)
                                              (:name body) (count initial)))
                   (= layouts (:parameter-layouts inference) (:parameter-layouts info))
                   (= guards (inference/parameter-guards layouts))
                   (= (:facts inference) (:facts info))
                   (= (select-keys info [:kind :result :temporary-escape :boundary :semantic-bridge :kernel-proof-attached?])
                      {:kind :private-accumulator :result :boolean :temporary-escape :rejected
                       :boundary :checked-pure-consumer :semantic-bridge :tested :kernel-proof-attached? false}))
      (reject! :admission))
    (bound! b owned)
    (diagnostics/phase :ownership-verify {} (affine/verify! owned derivation))
    artifact))

(def ^:private issue-edge
  (edge/trusted-issuer :enclosed-private-accumulator-v1 subject/core-contract
                      {:method :hosted-ownership-and-consumer-check :semantic-bridge :tested
                       :kernel-proof-attached? false}))

(defn plan
  ([b source] (plan b source {}))
  ([b source options]
  (let [a (diagnostics/phase :private-analysis {:pass :producer} (analyze b source))]
    ;; Diagnostic control adds the old repeated production. Both modes still
    ;; perform the same artifact/ownership check below.
    (when (true? (:repeat-private-analysis? options))
      (let [again (diagnostics/phase :private-analysis {:pass :repeat} (analyze b source))]
        (when-not (= a again) (fail :unstable-private-analysis))))
    (diagnostics/phase :private-analysis-check {} (check-analysis! b source a))
    (Endpoint. source (:owned a) (:derivation a)
               (issue-edge source (:owned a) (:info a)) (:guards a) (:info a) seal))))

(defn target [^Endpoint p] (.-owned p))
(defn accepted-edge [^Endpoint p] (.-accepted p))
(defn information [^Endpoint p] (.-info p))

(defn emit! [b p source]
  (when-not (and (endpoint? p) (= source (.-source ^Endpoint p))) (fail :private-source))
  (let [^Endpoint p p
        _ (bound! b (.-owned p))
        erased (diagnostics/phase :owned-erasure {:use :emission}
                 (erase/erase (.-owned p) (.-derivation p)
                            {:unbox-parameters? true :admitted-parameters? true
                             :parameter-layouts (:parameter-layouts (.-info p))}))
        form (:form erased)
        _ (budget/charge! b :bytes (alength (.getBytes (pr-str form) java.nio.charset.StandardCharsets/UTF_8)))
        _ (budget/charge! b :emissions 1)
        f (diagnostics/phase :host-compilation {:backend :private-clojure}
            (binding [*unchecked-math* false *ns* (the-ns 'klara.compile.affine-erase)] (eval form)))]
    {:run (fn [& args] (ev/invoke-boxed f args)) :abi :s12-v1 :form form
     :private-endpoint p :private-region (assoc (.-info p) :representations (:representations erased))
     :endpoint-guards (.-guards p)}))

(defn valid-executable? [exe]
  (let [p (:private-endpoint exe)]
    (and (endpoint? p)
         (= (:ir exe) (target p))
         (identical? (peek (:checked-edges exe)) (accepted-edge p))
         (every? (set (:guards exe)) (.-guards ^Endpoint p))
         (= (:private-region exe) (assoc (information p) :representations
                                         (:representations (diagnostics/phase :owned-erasure {:use :validation}
                                          (erase/erase (target p) (.-derivation ^Endpoint p)
                                           {:unbox-parameters? true :admitted-parameters? true
                                            :parameter-layouts (:parameter-layouts (information p))}))))))))
