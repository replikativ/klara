(ns klara.compile.emit
  "K1 -> Clojure forms -> host executable. Obligation: left-to-right
  evaluation and exact primitive behavior; reject unsupported control
  before execution. Lexical tail clauses call directly; abortive clauses
  unwind only their own instance. Self tail recursion uses JVM recur.
  General effects, ambient operations and escaping functions stay in T0."
  (:require [klara.compile.ir :as ir] [klara.eval :as ev]
            [klara.compile.runtime :as runtime]))

(defn unsupported [t reason]
  (throw (ex-info (str "compile: " reason) {:klara/error :compile :reason reason :op (:op t)})))

(defn emit-expr [t env tail? self]
  (let [go #(emit-expr % env false self)]
    (case (:op t)
      :quote (list 'quote (:datum t))
      :local (let [v (get env (:name t))]
               (if (symbol? v) v (unsupported t "function or handler escapes its local extent")))
      :prim (list* (symbol "clojure.core" (name (:name t))) (mapv go (:args t)))
      :let (let [s (:name t)]
             `(let [~s ~(go (:init t))] ~(emit-expr (:body t) (assoc env s s) tail? self)))
      :if `(if ~(go (:test t)) ~(emit-expr (:then t) env tail? self)
               ~(emit-expr (:else t) env tail? self))
      :letrec
      (if (and (= 1 (count (:inits t))) (not (:rest? (first (:inits t)))))
        (let [s (first (:names t)) f (first (:inits t)) ps (:params f)
              ctx (assoc env s {:recursive s :arity (:arity f)})
              body (emit-expr (:body f) (into ctx (map (juxt identity identity) ps)) true s)]
          `(letfn [(~s [~@ps] ~body)] ~(emit-expr (:body t) ctx tail? self)))
        (unsupported t "only single-function letrec is emitted"))
      :app
      (let [f (when (= :local (get-in t [:fn :op])) (get env (get-in t [:fn :name])))
            args (mapv go (:args t))]
        (if (and (:recursive f) (= (:arity f) (count args)))
          (if (= self (:recursive f))
            (if tail? (list* 'recur args) (unsupported t "non-tail recursive call"))
            (list* (:recursive f) args))
          (unsupported t "unknown or higher-order call")))
      :handle
      (if (and (= :lexical (:mode t)) (nil? (:return t))
               (not-any? #{:general} (vals (:classes t))))
        (let [token (gensym "extent") s (:name t)
              clauses (into {} (for [[op f] (:clauses t)
                                    :let [class (get (:classes t) op)
                                          ps (pop (:params f))
                                          body (if (= :tail-resumptive class) (first (:args (:body f))) (:body f))]]
                                [op {:arity (count ps) :class class :name (gensym "operation")
                                     :params ps :body (emit-expr body (into env (map (juxt identity identity) ps)) false nil)}]))
              e (gensym "abort")]
          `(let [~token (Object.)
                 ~@(mapcat (fn [[_ {:keys [name params body]}]] [name `(fn [~@params] ~body)]) clauses)]
             (try ~(emit-expr (:body t) (assoc env s {:token token :clauses clauses}) false self)
                  (catch clojure.lang.ExceptionInfo ~e
                    (if (identical? ~token (:klara.compile/extent (ex-data ~e)))
                      (:value (ex-data ~e)) (throw ~e))))))
        (unsupported t "general/dynamic/return handler remains in T0"))
      :perform
      (if (and (nil? (:target t)) (runtime/authority-ops (:name t)))
        `(runtime/authority-call ~(:name t) [~@(mapv go (:args t))])
       (let [h (get env (get-in t [:target :name])) cl (get-in h [:clauses (:name t)])]
        (if (and cl (= (:arity cl) (count (:args t))) (not= :general (:class t)))
          (let [call (list* (:name cl) (mapv go (:args t)))]
            (if (= :abortive (:class cl))
              `(throw (ex-info "compiled handler abort" {:klara.compile/extent ~(:token h) :value ~call})) call))
          (unsupported t "general or ambient operation remains in T0"))))
      (unsupported t (str "unsupported form " (:op t))))))

(defn run [term]
  (when (or (not= :fn (:op term)) (:rest? term)) (unsupported term "expected fixed-arity function"))
  (let [ps (:params term) args (gensym "args")
        body (emit-expr (:body term) (into {} (map (juxt identity identity) ps)) true nil)
        form `(fn [& ~args]
                (if (= ~(count ps) (count ~args))
                  (let [[~@ps] ~args] ~body)
                  klara.eval/deopt))]
    {:form form :run (eval form)}))
