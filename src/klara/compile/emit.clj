(ns klara.compile.emit
  "K1 -> Clojure forms -> host executable. Obligation: left-to-right
  evaluation and exact primitive behavior; reject unsupported control
  before execution. Lexical tail clauses call directly; abortive clauses
  unwind only their own instance. Self tail recursion uses JVM recur.
  General effects, ambient operations and escaping functions stay in T0."
  (:require [klara.compile.ir :as ir] [klara.compile.hof :as hof] [klara.eval :as ev]
            [klara.compile.runtime :as runtime] [klara.stage :as stage]
            [klara.world :as w] [klara.compile.unbox :as unbox]))

(defn unsupported [t reason]
  (throw (ex-info (str "compile: " reason) {:klara/error :compile :reason reason :op (:op t)})))

(def ^:dynamic *call-sites* nil)
(def ^:dynamic *context-symbol* nil)
(def ^:dynamic *return-layouts* {})

(declare emit-expr)

(defn emit-callback [f env arity]
  (when-not (and (= :fn (:op f)) (not (:rest? f)) (= arity (:arity f)))
    (unsupported f "HOF requires a known fixed-arity callback"))
  (let [ps (:params f)
        ;; A T0 host callback cannot perform on an enclosing lexical handler.
        ;; Keep only ordinary captured values; handlers inside f still work.
        env (into {} (filter (comp symbol? val)) env)]
    `(fn [~@ps] ~(emit-expr (:body f) (into env (map (juxt identity identity) ps)) true nil))))

(defn emit-hof [t env consumed?]
  (let [n (:name t) args (:args t) argc (count args)
        lazy? (contains? '#{map filter} n)
        arity (if (= 'reduce n) 2 1)
        expected (if (= 'reduce n) 3 2)]
    (when-not (= expected argc)
      (unsupported t "unsupported HOF arity (no transducers or multi-collection calls)"))
    (when (and lazy? (not consumed?))
      (unsupported t "lazy callback must be consumed eagerly in the same expression"))
    (let [f (first args) callback (emit-callback f env arity)
          coll (last args)
          emit #(emit-expr % env false nil)
          collection (emit-expr coll env false nil true)
          vector? (or (and (= :prim (:op coll)) (= 'vector (:name coll)))
                      (and (= :quote (:op coll))
                           (= clojure.lang.PersistentVector (class (:datum coll)))))]
      (if (contains? '#{reduce mapv} n)
        ;; Exact PersistentVector identity licenses indexed traversal; other
        ;; inputs keep their public host traversal without probing their seq.
        ;; Bind all arguments before iteration, including reducer init, and
        ;; inline the closure body at the loop site (no callback IFn call).
        (let [xs (gensym "vector") init (gensym "init") i (gensym "index")
              acc (gensym "acc") result (gensym "result") ps (:params f)
              body-env (into (into {} (filter (comp symbol? val)) env)
                             (map (juxt identity identity) ps))
              body (emit-expr (:body f) body-env false nil)
              bindings (if (= 'reduce n) [init (emit (second args)) xs collection] [xs collection])
              fallback (if (= 'reduce n) `(reduce ~callback ~init ~xs) `(mapv ~callback ~xs))
              loop-form `(loop [~i 0 ~acc ~(if (= 'reduce n) init [])]
               (if (< ~i (count ~xs))
                 (let [~@(if (= 'reduce n)
                           [(first ps) acc (second ps) `(nth ~xs ~i)]
                           [(first ps) `(nth ~xs ~i)])
                       ~result ~body]
                   ~(if (= 'reduce n)
                      `(if (reduced? ~result) @~result (recur (inc ~i) ~result))
                      `(recur (inc ~i) (conj ~acc ~result))))
                 ~acc))]
          `(let [~@bindings]
             ~(if vector? loop-form
                `(if (= clojure.lang.PersistentVector (class ~xs)) ~loop-form ~fallback))))
        ;; Public host traversal preserves IReduce/IKVReduce, reduced handling,
        ;; chunking, short circuiting and exceptions for arbitrary inputs.
        (list* (symbol "clojure.core" (name n)) callback
               (if (= 'reduce n) [(emit (second args)) collection] [collection]))))))

(defn emit-expr
  ([t env tail? self] (emit-expr t env tail? self false))
  ([t env tail? self consumed?]
  (let [go #(emit-expr % env false self)]
    (case (:op t)
      :quote (list 'quote (:datum t))
      :local (let [v (get env (:name t))]
               (if (symbol? v) v (unsupported t "function or handler escapes its local extent")))
      :numeric-guard
      (let [[a b] (mapv go (:args t))
            both? (ir/trivial? (second (:args t)))]
        `(if (and (:feedback ~*context-symbol*)
                  (not (stage/speculate-key? (:feedback ~*context-symbol*) '~[[(:code-id t) (:site t)] :deopt])))
           (+ ~a ~b)
           (if (and (instance? Long ~a) ~(if both? `(instance? Long ~b) true))
             (+ (long ~a) ~(if both? `(long ~b) b))
             (ev/deopt! 0 [~@(mapv go (:live t))]))))
      :loop-check
      (let [body (emit-expr (:body t) env tail? self)]
        `(if (or (and (:feedback ~*context-symbol*)
                      (not (stage/speculate-key? (:feedback ~*context-symbol*) '~[[(:code-id t) (:site t)] :deopt])))
                 (and ~@(map (fn [a] `(instance? Long ~(go a))) (:args t))))
           ~body
           (ev/deopt! 0 [~@(mapv go (:live t))])))
      :prim (cond
              (hof/callbacks (:name t)) (emit-hof t env consumed?)
              (and (= 'vec (:name t)) (= 1 (count (:args t))))
              `(vec ~(emit-expr (first (:args t)) env false self true))
              (= 'into (:name t))
              (if (= 2 (count (:args t)))
                `(into ~(go (first (:args t))) ~(emit-expr (second (:args t)) env false self true))
                (unsupported t "only two-argument into is supported"))
              :else (list* (symbol "clojure.core" (name (:name t))) (mapv go (:args t))))
      :let (let [s (:name t)]
             `(let [~s ~(go (:init t))] ~(emit-expr (:body t) (assoc env s s) tail? self)))
      :if `(if ~(go (:test t)) ~(emit-expr (:then t) env tail? self)
               ~(emit-expr (:else t) env tail? self))
      :letrec
      (if (and (= 1 (count (:inits t))) (not (:rest? (first (:inits t)))))
        (let [s (first (:names t)) f (first (:inits t)) ps (:params f)
              ctx (assoc env s {:recursive s :arity (:arity f)})
              loop-env (into ctx (map (juxt identity identity) ps))
              body (emit-expr (:body f) loop-env true s)
              fast-body (emit-expr (if (= :loop-check (:op (:body f)))
                                    (:body (:body f)) (:body f)) loop-env true s)
              kinds (unbox/loop-kinds t *return-layouts*)
              generic `(letfn [(~s [~@ps] ~body)] ~(emit-expr (:body t) ctx tail? self))]
          (if (seq kinds)
            (let [args (mapv (fn [_] (gensym "initial")) ps)
                  fallback `(letfn [(~s [~@ps] ~body)] (~s ~@args))]
              `(let [~@(mapcat vector args (mapv go (get-in t [:body :args])))]
                 ~(reduce (fn [other kind]
                            `(if (and ~@(map (fn [a] `(instance? ~(if (= kind :long) 'Long 'Double) ~a)) args))
                               (loop [~@(mapcat (fn [p a] [p (list (symbol "clojure.core" (name kind)) a)]) ps args)]
                                 ~fast-body)
                               ~other)) fallback (reverse kinds))))
            generic))
        (unsupported t "only single-function letrec is emitted"))
      :app
      (let [f (when (= :local (get-in t [:fn :op])) (get env (get-in t [:fn :name])))
            args (mapv go (:args t))]
        (cond
          (and (:recursive f) (= (:arity f) (count args)))
          (if (= self (:recursive f))
            (if tail? (list* 'recur args) (unsupported t "non-tail recursive call"))
            (list* (:recursive f) args))
          (= :resolve (get-in t [:fn :op]))
          (let [site (gensym "callsite") resolved (gensym "callee")]
            (swap! *call-sites* conj [site (get-in t [:fn :id])])
            `(let [~resolved (~site ~*context-symbol*)]
               (stage/context-call ~site ~*context-symbol* ~resolved ~@args)))
          :else (unsupported t "unknown or higher-order call")))
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
        `(runtime/authority-call ~*context-symbol* ~(:name t) [~@(mapv go (:args t))])
       (let [h (get env (get-in t [:target :name])) cl (get-in h [:clauses (:name t)])]
        (if (and cl (= (:arity cl) (count (:args t))) (not= :general (:class t)))
          (let [call (list* (:name cl) (mapv go (:args t)))]
            (if (= :abortive (:class cl))
              `(throw (ex-info "compiled handler abort" {:klara.compile/extent ~(:token h) :value ~call})) call))
          (unsupported t "general or ambient operation remains in T0"))))
      (unsupported t (str "unsupported form " (:op t)))))))

(defn run
  ([term] (run term #{}))
  ([term reads] (run term reads {}))
  ([term reads return-layouts]
   (when (or (not= :fn (:op term)) (:rest? term)) (unsupported term "expected fixed-arity function"))
   (let [ps (:params term) sites (atom []) ctx (gensym "context")
         body (binding [*call-sites* sites *context-symbol* ctx
                        *return-layouts* return-layouts]
                (emit-expr (:body term) (into {} (map (juxt identity identity) ps)) true nil))
         body-name (gensym "body")
         read-set (set (for [[_ s h] reads] [:value s h]))
         ;; Preserve the public boxed :run and independently evaluable :form.
         ;; Explicit context is a private physical extension of the S12 ABI.
         factory (if (< (count ps) 20)
                   `(let [~@(mapcat (fn [[site sym]] [site `(stage/make-world-call-site '~sym)]) @sites)
                          ~body-name (fn [~ctx ~@ps] ~body)]
                      {:run (fn [~@ps]
                              ~@(for [r read-set] `(w/note-read! '~r))
                              (~body-name (stage/current-context) ~@ps))
                       :invoke ~body-name})
                   `(let [~@(mapcat (fn [[site sym]] [site `(stage/make-world-call-site '~sym)]) @sites)]
                      {:run (fn [~@ps]
                              ~@(for [r read-set] `(w/note-read! '~r))
                              (let [~ctx (stage/current-context)] ~body))}))
         runners (eval factory)]
     (merge runners {:form `(:run ~factory) :abi :s12-v1
                     :definition-reads read-set}))))
