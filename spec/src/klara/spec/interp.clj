(ns klara.spec.interp
  "Front end and driver for the compiled reference semantics.

  `parse` turns a named surface program (EDN) into the de Bruijn `Tm` of
  klara.spec.core, `run` iterates the kernel-checked `step` (compiled to
  Clojure by ansatz) and `observe` reports the final configuration as EDN.

  Nothing here is verified: it is the (small) trusted bridge between data
  programs and the spec. The runtime representation it builds is ansatz's
  codegen representation of the inductives (see `rep` below).

  Surface grammar (programs are plain EDN, so the same files can drive the
  T0 interpreter in klara/src):

    nil true false 42           datum literal  (quote d) also accepted
    x                           local
    (fn [x y] e)                curried: (fn [x] (fn [y] e))
    (f a b)                     curried: ((f a) b)
    (let [x e1 y e2] b)         nested lets
    (if c t e)                  Clojure truthiness
    (letrec [f (fn [x] e)] b)   one recursive function (curried params ok)
    (resolve :id)               global read from the world
    (prim op a b)               op in + - * = <
    (perform h :op v)           h a capability; h = nil for an ambient op
    (handle [h] body {:return (fn [x] r) :op1 (fn [v k] e) ...})
    (specialize p m)
    (code e)                    staging (S5): bracket
    (esc e)                     splice (inside code)
    (run e)                     run closed code"
  (:require [klara.spec.core :as k]))

;; ---------------------------------------------------------------------------
;; Runtime representation (ansatz codegen, ansatz 2026-10 main):
;;   Datum, Tm, Stuck, Out: tagged vectors [ctor-index field...]
;;   PrimOp (all constructors nullary): nil for index 0, else the index
;;   World (empty | bind): nil | [id v rest];  Config: [w fresh t]
;;   Option: nil | [x]

(def ^:private tm-tag
  {:var 0 :lit 1 :lam 2 :app 3 :let 4 :if 5 :letrec 6 :resolve 7 :prim 8
   :perform 9 :handle 10 :specialize 11 :fix 12 :cap 13 :handling 14
   :code 15 :esc 16 :run 17 :gvar 18 :nlam 19 :nlet 20 :nletrec 21 :nhandle 22})

(def ^:private tag-name (zipmap (vals tm-tag) (keys tm-tag)))

(defn- tm [tag & fields] (into [(tm-tag tag)] fields))

(defn datum [d]
  (cond (nil? d) [0]
        (boolean? d) [1 d]
        (integer? d) [2 (bigint d)]
        :else (throw (ex-info "not a datum (nil, boolean or integer)" {:datum d}))))

(def ^:private prim-op {'+ nil '- 1 '* 2 '= 3 '< 4})

;; ---------------------------------------------------------------------------
;; Parsing (names -> de Bruijn)

(defn- intern! [table kw]
  (or (get @table kw)
      (let [i (count @table)] (swap! table assoc kw i) i)))

(declare parse*)

(defn- index-of [env x]
  (let [i (.lastIndexOf ^java.util.List env x)]
    (when (neg? i) (throw (ex-info (str "unbound local " x) {:local x})))
    (- (count env) 1 i)))

(defn- lams [ctx env params body]
  (if (empty? params)
    (parse* ctx env body)
    (tm :lam (lams ctx (conj env (first params)) (rest params) body))))

(defn- handler-clause
  "Compile {:return r, :op1 c1, ...} into the single op clause of `handle`,
  which binds [op v k] and dispatches on the op tag. An op the instance does
  not define is a front-end choice: it applies nil, i.e. stuck :not-fn."
  [ctx env clauses]
  (let [ops (dissoc clauses :return)
        env3 (conj env '%op '%v '%k)
        call (fn [clause]
               ;; ((clause v) k) with clause closed over env, evaluated under [op v k]
               (let [c (parse* ctx env3 clause)]
                 (tm :app (tm :app c (tm :var 1)) (tm :var 0))))]
    (reduce (fn [else [op clause]]
              (tm :if (tm :prim (prim-op '=) (tm :var 2) (tm :lit (datum (intern! (:ops ctx) op))))
                  (call clause)
                  else))
            (tm :app (tm :lit (datum nil)) (tm :lit (datum nil)))
            (reverse (sort-by key ops)))))

(defn- parse* [ctx env form]
  (cond
    (or (nil? form) (boolean? form) (integer? form)) (tm :lit (datum form))
    (symbol? form) (tm :var (index-of env form))
    (seq? form)
    (let [[head & args] form]
      (case head
        quote (tm :lit (datum (first args)))
        fn (let [[params body] args] (lams ctx env params body))
        let (let [[bs body] args]
              (if (empty? bs)
                (parse* ctx env body)
                (let [[x e & more] bs]
                  (tm :let (parse* ctx env e)
                      (parse* ctx (conj env x) (list 'let (vec more) body))))))
        if (let [[c t e] args]
             (tm :if (parse* ctx env c) (parse* ctx env t) (parse* ctx env e)))
        letrec (let [[[f [fn-sym [p & ps] fbody]] body] args]
                 (assert (= 'fn fn-sym) "letrec binds a (fn [x ...] e)")
                 (tm :letrec (lams ctx (conj env f p) ps fbody)
                     (parse* ctx (conj env f) body)))
        resolve (tm :resolve (intern! (:ids ctx) (first args)))
        prim (let [[op x y] args]
               (assert (contains? prim-op op) (str "unknown prim " op))
               (tm :prim (prim-op op) (parse* ctx env x) (parse* ctx env y)))
        perform (let [[h op x] args]
                  (tm :perform (intern! (:ops ctx) op) (parse* ctx env h) (parse* ctx env x)))
        handle (let [[[h] body clauses] args
                     [_ [x] r] (:return clauses '(fn [x] x))]
                 (tm :handle (parse* ctx (conj env h) body)
                     (parse* ctx (conj env x) r)
                     (handler-clause ctx env clauses)))
        specialize (let [[p m] args] (tm :specialize (parse* ctx env p) (parse* ctx env m)))
        code (tm :code (parse* ctx env (first args)))
        esc (tm :esc (parse* ctx env (first args)))
        run (tm :run (parse* ctx env (first args)))
        ;; application, curried
        (reduce (fn [f a] (tm :app f (parse* ctx env a)))
                (parse* ctx env head) args)))
    :else (throw (ex-info "unsupported form" {:form form}))))

(defn- fresh-ctx [] {:ops (atom {}) :ids (atom {})})

(defn parse
  "Parse a program; returns {:tm Tm :world World :ops {kw n} :ids {kw n}}."
  ([form] (parse form {}))
  ([form world]
   (let [ctx (fresh-ctx)
         t (parse* ctx [] form)
         w (reduce (fn [w [id v]] [(intern! (:ids ctx) id) (parse* ctx [] v) w])
                   nil (sort-by key world))]
     {:tm t :world w :ops @(:ops ctx) :ids @(:ids ctx)})))

;; ---------------------------------------------------------------------------
;; Running and observing

(defn decode-datum [[tag x]]
  (case (int tag) 0 nil 1 x 2 (let [i (bigint x)] (if (< (abs i) Long/MAX_VALUE) (long i) i))))

(defn tm->edn
  "A de Bruijn Tm as readable EDN: [:lam [:app [:var 0] [:lit 1]]]. Op tags
  and world ids stay numbers. Used to compare generated code with T0."
  [t]
  (let [[tag & fs] t
        nm (tag-name (int tag))]
    (case nm
      :lit [:lit (decode-datum (first fs))]
      (:var :resolve :gvar :cap) [nm (long (first fs))]
      :prim [:prim ({nil '+ 1 '- 2 '* 3 '= 4 '<} (some-> (first fs) int)) (tm->edn (nth fs 1)) (tm->edn (nth fs 2))]
      :perform (into [:perform (long (first fs))] (map tm->edn (rest fs)))
      (:handling :nlam :nlet :nletrec :nhandle) (into [nm (long (first fs))] (map tm->edn (rest fs)))
      (into [nm] (map tm->edn fs)))))

(defn decode-code
  "Observation of a code value: its term in de Bruijn form, or :klara/open-code
  when it mentions a generated name that no binder inside it binds."
  [u]
  (let [d (k/toDB u)]
    (if ((k/wsbF d) 0)
      {:klara/code (tm->edn d)}
      :klara/open-code)))

(defn decode-value [v]
  (case (int (first v))
    1 (decode-datum (second v))
    (2 12) :klara/fn
    13 :klara/cap
    15 (decode-code (second v))
    {:klara/term v}))

(def ^:private stuck-name {0 :scope 1 :not-fn 2 :prim-type 3 :bad-target 4 :unbound
                           5 :stage 6 :lift 7 :scope-extrusion})

(defn observe
  "Classify a terminal configuration."
  [[w n t :as c] {:keys [ops ids]}]
  (let [out (k/run1 w n t)
        op-name (fn [i] (get (zipmap (vals ops) (keys ops)) i i))]
    (case (int (first out))
      0 {:value (decode-value t)}
      1 {:running c}
      2 (let [[_ tg op _v _k] out]
          (if (nil? tg)
            {:stuck :unhandled-op :op (op-name op)}
            {:stuck :unhandled-instance :op (op-name op)}))
      3 (let [[_ [s id]] out]
          (cond-> {:stuck (stuck-name (int s))}
            (= 4 (int s)) (assoc :id (get (zipmap (vals ids) (keys ids)) id id))))
      ;; a splice of code that mentions a dead generated name
      4 {:stuck :scope-extrusion})))

(defn run
  "Run program `form` (with optional world map) for at most `fuel` steps.
  Returns the observation plus the number of steps taken."
  ([form] (run form {} 100000))
  ([form world] (run form world 100000))
  ([form world fuel]
   (let [{:keys [tm world] :as p} (parse form world)]
     (loop [c [world 0 tm] steps 0]
       (if (>= steps fuel)
         {:fuel-exhausted true :steps steps}
         (if-let [[c'] (k/step c)]
           (recur c' (inc steps))
           (assoc (observe c p) :steps steps)))))))
