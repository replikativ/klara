(ns klara.compile.scalar
  "Conservative checked Long/Boolean region analysis and Java emission.
   Pure scalar expressions and single-entry tail loops only. Rejection is
   an ordinary tier decline; this tested seed compiler is not a proof."
  (:require [clojure.string :as str]
            [klara.compile.requirements :as requirements]
            [klara.compile.analysis :as analysis]))

(defn fail [t why] (throw (ex-info why {:op (:op t) :reason :unsupported-region})))
(defn require-type [t type]
  (when-not (= type (:type t)) (fail t (str "expected " type))) t)

(declare analyze)
(defn analyze [t env summaries recur-info]
  (let [go #(analyze % env summaries recur-info)
        result
        (case (:op t)
          :quote (cond (instance? Long (:datum t)) (assoc t :type :long)
                       (boolean? (:datum t)) (assoc t :type :boolean)
                       :else (fail t "only Long/Boolean constants"))
          :local (if-let [k (get env (:name t))] (assoc t :type k)
                     (fail t "unknown local"))
          :prim (let [args (mapv go (:args t)) n (:name t)
                      unary? (contains? '#{inc dec} n)
                      numeric? (contains? '#{+ - * inc dec} n)
                      compare? (contains? '#{< > <= >= =} n)]
                  (when-not (and (or numeric? compare?)
                                 (= (if unary? 1 2) (count args)))
                    (fail t "unsupported primitive/arity"))
                  (doseq [a args] (require-type a :long))
                  (assoc t :args args :type (analysis/scalar-result n (mapv :type args))))
          :let (let [init (go (:init t))
                     body (analyze (:body t) (assoc env (:name t) (:type init)) summaries recur-info)]
                 (assoc t :init init :body body :type (:type body)))
          :if (let [test (require-type (go (:test t)) :boolean)
                    a (go (:then t)) b (go (:else t))
                    k (cond (= :bottom (:type a)) (:type b)
                            (= :bottom (:type b)) (:type a)
                            (= (:type a) (:type b)) (:type a)
                            :else (fail t "incompatible branches"))]
                (assoc t :test test :then a :else b :type k))
          :loop-check (assoc (go (:body t)) :discharged-check :loop-layout)
          :app (let [args (mapv go (:args t)) target (:fn t)]
                 (cond
                   (and recur-info (= :local (:op target))
                        (= (:name target) (:name recur-info)))
                   (do (when-not (= (:types recur-info) (mapv :type args))
                         (fail t "backedge does not preserve invariant"))
                       (assoc t :op :recur :args args :type :bottom))
                   (= :resolve (:op target))
                   (let [summary (get summaries (:id target))]
                     (when-not (and summary (= (:args summary) (mapv :type args)))
                       (fail t "callee layout not established"))
                     (assoc t :args args :type (:return summary)))
                   :else (fail t "unknown call")))
          :letrec
          (let [f (first (:inits t)) entry (:body t) name (first (:names t))]
            (when-not (and (= 1 (count (:inits t))) (= :fn (:op f))
                           (not (:rest? f)) (= :app (:op entry))
                           (= {:op :local :name name} (:fn entry))
                           (= (:arity f) (count (:args entry))))
              (fail t "expected directly entered single tail loop"))
            (let [args (mapv go (:args entry)) types (mapv :type args)
                  body (analyze (:body f) (merge env (zipmap (:params f) types))
                                summaries {:name name :types types})]
              (when (= :bottom (:type body)) (fail t "loop has no typed return"))
              (assoc t :op :loop :params (:params f) :args args :body body
                     :invariant types :type (:type body))))
          (fail t "unsupported region operation"))]
    result))

(defn typed-function [exe summaries]
  (let [t (:ir exe)]
    (when-not (and (= :fn (:op t)) (not (:rest? t))) (fail t "fixed function required"))
    (let [types (vec (repeat (:arity t) :long))
          body (analyze (:body t) (zipmap (:params t) types) summaries nil)]
      (require-type body :long)
      {:params (:params t) :body body :args types :return :long
       :requirements (requirements/from-executable exe types)
       :requires (mapv (fn [i] [:argument-class i 'Long]) (range (:arity t)))
       :dependencies (set (filter #(= :world (first %)) (:guards exe)))
       :effects #{:checked-arithmetic-exception}})))

(defn java-type [k] (case k :long "long" :boolean "boolean"))
(def ^:dynamic *counter* nil)
(declare expression tail-code)
(defn fresh [] (str "t" (swap! *counter* inc)))

(defn expression [t env functions inline?]
  (let [go #(expression % env functions inline?)
        bind-result (fn [statements value]
                      (let [v (fresh)]
                        [(str statements (java-type (:type t)) " " v " = " value ";\n") v]))]
    (case (:op t)
      :quote ["" (if (= :boolean (:type t)) (str (:datum t))
                     (str (:datum t) "L"))]
      :local ["" (get env (:name t))]
      :let (let [[a v] (go (:init t))
                 [b result] (expression (:body t) (assoc env (:name t) v) functions inline?)]
             [(str a b) result])
      :if (let [[s p] (go (:test t)) v (fresh)
                [a av] (go (:then t)) [b bv] (go (:else t))]
            [(str s (java-type (:type t)) " " v ";\nif (" p ") {\n"
                  a v " = " av ";\n} else {\n" b v " = " bv ";\n}\n") v])
      (:prim :app)
      (let [pairs (mapv go (:args t)) statements (apply str (map first pairs))
            vs (mapv second pairs)]
        (if (= :prim (:op t))
          (bind-result statements
                       (if-let [method (get {'+ "addExact" '- "subtractExact" '* "multiplyExact"
                                             'inc "incrementExact" 'dec "decrementExact"} (:name t))]
                         (str "Math." method "(" (str/join "," vs) ")")
                         (str "(" (first vs) " " (if (= '= (:name t)) "==" (name (:name t)))
                              " " (second vs) ")")))
          (let [sym (get-in t [:fn :id]) callee (get functions sym)]
            (if inline?
              (let [[s v] (expression (:body callee) (zipmap (:params callee) vs) functions inline?)]
                [(str statements s) v])
              (bind-result statements (str "direct_" sym "(" (str/join "," vs) ")"))))))
      (fail t "non-scalar expression in scalar position"))))

(defn tail-code [t env functions inline? loop-info]
  (let [go #(tail-code % env functions inline? loop-info)]
    (case (:op t)
      :let (let [[s v] (expression (:init t) env functions inline?)]
             (str s (tail-code (:body t) (assoc env (:name t) v) functions inline? loop-info)))
      :if (let [[s p] (expression (:test t) env functions inline?)]
            (str s "if (" p ") {\n" (go (:then t)) "} else {\n" (go (:else t)) "}\n"))
      :loop (let [pairs (mapv #(expression % env functions inline?) (:args t))
                  ps (mapv (fn [_] (fresh)) (:params t)) label (fresh)
                  setup (apply str (map first pairs))]
              (str setup
                   (apply str (map (fn [p a k] (str (java-type k) " " p " = " (second a) ";\n"))
                                   ps pairs (:invariant t)))
                   label ": while (true) {\n"
                   (tail-code (:body t) (merge env (zipmap (:params t) ps)) functions inline?
                              {:params ps :label label}) "}\n"))
      :recur (let [pairs (mapv #(expression % env functions inline?) (:args t))
                   ;; Bind every argument before assigning any loop local.
                   temps (mapv (fn [_] (fresh)) pairs)]
               (when-not loop-info (fail t "recur outside loop"))
               (str (apply str (map first pairs))
                    (apply str (map (fn [v p a] (str (java-type (:type a)) " " v " = " (second p) ";\n"))
                                    temps pairs (:args t)))
                    (apply str (map #(str %1 " = " %2 ";\n") (:params loop-info) temps))
                    "continue " (:label loop-info) ";\n"))
      (let [[s v] (expression t env functions inline?)] (str s "return " v ";\n")))))
