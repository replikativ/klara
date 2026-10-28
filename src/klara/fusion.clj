(ns klara.fusion
  "S3: map/filter/reduce fusion as a law-licensed rewrite with an ansatz
  certificate, installed through Klara's specialization cache.

  PIPELINE (doc/06 §3, 'pass correctness' and 'guarded specialization'):

    Klara core term of (fn [xs] (reduce f init (map g (filter p xs))))
       │ elaborate          gated on a checked shape claim; stages must
       ▼                    elaborate into ansatz (hence are pure)
    ansatz term  λ xs : List Nat. foldl F I (map G (filter Q xs))
       │ fuse               Klara.foldl_map / Klara.foldl_filter at the root,
       ▼                    chained by Eq.trans: a proof of naive = fused
    ansatz term  λ xs. foldl F' I xs           (one pass)
       │ lower              exact-or-throw JVM arithmetic; any
       ▼                    ArithmeticException declines (deopt) at entry
    host fn, installed under (CodeId of the Klara fn, guards) with a
    certificate that klara.stage/install! rechecks through the
    :ansatz/kernel checker registered here.

  À LA CARTE. Nothing is elaborated without a shape claim: (claim! s 'p
  '{:args [(List Nat)] :ret Nat}) publishes the world definition p$shape.
  Unclaimed code stays generic. The claim is CHECKED: its argument part
  becomes the entry guard [:arg 0 :nat-list]; its result part is checked
  by the kernel when it types the elaborated term.

  THE FRAGMENT. Sources: the parameter. Stages: map, filter (any number,
  any order) and a final reduce with an init, or reduce + / * without one.
  A stage is an inline fn, a world definition holding a fn (inlined, its
  version becomes a guard), or + * inc ... in value position. Stage
  bodies: locals, non-negative integer and boolean literals, if, let,
  calls of elaboratable world fns, and the prims
    + * inc quot rem mod < > <= >= = not= zero? pos? even? odd? not identity.
  Anything else — an effect, a host call, `-`/`dec` (Nat subtraction
  truncates, longs do not), a recursive helper — makes the stage OPAQUE,
  and an opaque stage blocks fusion: the pipeline stays generic and the
  report names the stage.

  OVERFLOW (doc/06 §4). The laws are proved over Nat; the executable runs
  on longs. The lowering maps every Nat operation to a JVM operation that
  returns the Nat result or throws (Math/addExact, multiplyExact,
  incrementExact, quot, rem; comparisons are exact). The executable
  catches ArithmeticException and returns klara.eval/deopt, so the
  generic path runs from entry; that replay is sound because elaborated
  stages perform no effects. Hence whenever the executable returns a
  value, that value is the Nat meaning of the fused term, which the
  theorem equates with the Nat meaning of the naive term. The generic
  path computes with clojure.core arithmetic, which on non-negative longs
  is likewise exact-or-throw. The remaining trusted step: the two paths
  overflow on the same inputs. It holds for these laws because fusion is
  OPERATION-PRESERVING — the fused step applies the same stage functions
  to the same values in the same order per element — so both perform the
  same multiset of arithmetic operations; it is recorded in the
  certificate as a side condition with status :trusted, and property
  tested near Long/MAX_VALUE."
  (:require [klara.core :as kc]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]
            [klara.stage :as s]
            [klara.fusion.kernel :as k]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]))

(def elaborator-version "klara.fusion/1")

(defn claim-sym "The world name holding sym's shape claim." [sym] (symbol (str sym "$shape")))

(def supported-claim '{:args [(List Nat)] :ret Nat})

;; ---------------------------------------------------------------------------
;; elaboration: Klara core terms -> ansatz terms
;; ---------------------------------------------------------------------------

(defn- opaque! [reason & {:as data}]
  (throw (ex-info (str "opaque: " (pr-str reason)) (assoc data ::opaque reason))))

(def ^:private Nat k/Nat)
(defn- nat-lit [n] (e/lit-nat (biginteger n)))
(defn- ap [n & args] (apply e/app* (k/c n) args))
(def ^:private btrue (k/c "Bool.true"))
(def ^:private bfalse (k/c "Bool.false"))

(defn- typed [ty x] {:type ty :expr x})

(defn- want [ty {:keys [type expr] :as v} what]
  (when-not (= ty type) (opaque! [:type what type :expected ty]))
  expr)

(def ^:private ops
  "Klara prim name -> (fn [args]) of elaborated {:type :expr} args."
  (letfn [(nats [op args] (mapv #(want :nat % op) args))
          (n-ary [op unit cst]
            (fn [args] (let [xs (nats op args)]
                         (typed :nat (if (empty? xs) (nat-lit unit) (reduce #(ap cst %1 %2) xs))))))
          (unary [op f] (fn [args] (when-not (= 1 (count args)) (opaque! [:arity op]))
                          (f (want :nat (first args) op))))
          (binary [op f] (fn [args] (when-not (= 2 (count args)) (opaque! [:arity op]))
                           (let [[a b] (nats op args)] (f a b))))]
    {'+ (n-ary '+ 0 "Nat.add")
     '* (n-ary '* 1 "Nat.mul")
     'inc (unary 'inc #(typed :nat (ap "Nat.succ" %)))
     'quot (binary 'quot #(typed :nat (ap "Nat.div" %1 %2)))
     'rem (binary 'rem #(typed :nat (ap "Nat.mod" %1 %2)))
     'mod (binary 'mod #(typed :nat (ap "Nat.mod" %1 %2)))
     '< (binary '< #(typed :bool (ap "Nat.blt" %1 %2)))
     '> (binary '> #(typed :bool (ap "Nat.blt" %2 %1)))
     '<= (binary '<= #(typed :bool (ap "Nat.ble" %1 %2)))
     '>= (binary '>= #(typed :bool (ap "Nat.ble" %2 %1)))
     '= (binary '= #(typed :bool (ap "Nat.beq" %1 %2)))
     'not= (binary 'not= #(typed :bool (ap "Bool.not" (ap "Nat.beq" %1 %2))))
     'zero? (unary 'zero? #(typed :bool (ap "Nat.beq" % (nat-lit 0))))
     'pos? (unary 'pos? #(typed :bool (ap "Nat.blt" (nat-lit 0) %)))
     'even? (unary 'even? #(typed :bool (ap "Nat.beq" (ap "Nat.mod" % (nat-lit 2)) (nat-lit 0))))
     'odd? (unary 'odd? #(typed :bool (ap "Nat.beq" (ap "Nat.mod" % (nat-lit 2)) (nat-lit 1))))
     'not (fn [args] (when-not (= 1 (count args)) (opaque! [:arity 'not]))
            (typed :bool (ap "Bool.not" (want :bool (first args) 'not))))
     'identity (fn [args] (when-not (= 1 (count args)) (opaque! [:arity 'identity]))
                 (first args))}))

(defn- host-op? [t opname sym]
  (and (= :perform (:op t)) (nil? (:target t)) (= opname (:name t))
       (= {:op :quote :datum sym} (first (:args t)))))

(defn- host-var-prim
  "The prim named by a value-position host var clojure.core/x, if any."
  [t]
  (when (and (= :perform (:op t)) (nil? (:target t)) (= :host/var (:name t)))
    (let [d (:datum (first (:args t)))]
      (when (and (qualified-symbol? d) (= "clojure.core" (namespace d)) (ops (symbol (name d))))
        (symbol (name d))))))

(defn- resolve-fn-def
  "The fn term of world definition sym, recording it as a dependency."
  [ctx sym]
  (let [{:keys [term] :as dep} ((:resolve-def ctx) sym)]
    (when-not dep (opaque! [:unresolvable sym]))
    (when-not (= :fn (:op term)) (opaque! [:not-a-fn-definition sym]))
    term))

(declare elab-expr)

(defn- elab-call
  "Apply the Klara callable term f (fn term, world fn, or prim value) to
  elaborated args, inlining (stages are pure and terminating)."
  [ctx env f args]
  (cond
    (= :fn (:op f))
    (do (when (or (:rest? f) (not= (:arity f) (count args))) (opaque! [:arity-mismatch]))
        ;; a fn term inside a stage may close over enclosing locals
        (elab-expr ctx (:body f) (into env args)))

    (= :resolve (:op f))
    (let [sym (:id f)]
      (when (contains? (:inlining ctx) sym) (opaque! [:recursive sym]))
      (let [ft (resolve-fn-def ctx sym)]
        ;; a world definition is closed: its body sees only its own params
        (elab-call (update ctx :inlining (fnil conj #{}) sym) [] ft args)))

    (host-var-prim f) ((ops (host-var-prim f)) args)

    :else (opaque! [:callee (:op f)])))

(defn- elab-expr
  "Elaborate a Klara core term under env (a vector of {:type :expr}, last
  = de Bruijn index 0) to {:type :nat|:bool :expr Expr}."
  [ctx t env]
  (case (:op t)
    :local (let [v (nth env (- (count env) 1 (:index t)))]
             (when-not (#{:nat :bool} (:type v)) (opaque! [:local-of-type (:type v)]))
             v)
    :quote (let [x (:datum t)]
             (cond (and (instance? Long x) (>= (long x) 0)) (typed :nat (nat-lit x))
                   (true? x) (typed :bool btrue)
                   (false? x) (typed :bool bfalse)
                   :else (opaque! [:literal x])))
    :prim (if-let [f (ops (:name t))]
            (f (mapv #(elab-expr ctx % env) (:args t)))
            (opaque! [:prim (:name t)]))
    :if (let [c (want :bool (elab-expr ctx (:test t) env) 'if)
              a (elab-expr ctx (:then t) env)
              b (elab-expr ctx (:else t) env)]
          (when-not (= (:type a) (:type b)) (opaque! [:if-branches (:type a) (:type b)]))
          (typed (:type a) (k/cond* (if (= :nat (:type a)) Nat k/Bool) c (:expr a) (:expr b))))
    ;; pure, so let is substitution
    :let (elab-expr ctx (:body t) (conj env (elab-expr ctx (:init t) env)))
    :app (elab-call ctx env (:fn t) (mapv #(elab-expr ctx % env) (:args t)))
    (opaque! [:form (:op t) (when (= :perform (:op t)) (:name t))])))

(defn- elab-stage-fn
  "Elaborate stage callable t (in pipeline env) as an ansatz lambda over
  Nat params with result type ret."
  [ctx env t n ret]
  (let [ids (vec (repeatedly n k/fvar!))
        args (mapv #(typed :nat (e/fvar %)) ids)
        body (want ret (elab-call ctx env t args) [:stage-result])]
    (k/lam* (mapv (fn [id i] [id (str "x" i) Nat]) ids (range)) body)))

(defn- elab-source
  "Parse a list-valued pipeline term into [[kind callable-term] ..]
  (outermost first) ending at the parameter."
  [t depth]
  (cond
    (= {:op :local :index (dec depth)} t) []
    (host-op? t :host/call 'clojure.core/map)
    (let [[_ g src & more] (:args t)]
      (when (seq more) (opaque! [:map-arity]))
      (into [[:map g]] (elab-source src depth)))
    (host-op? t :host/call 'clojure.core/filter)
    (let [[_ q src & more] (:args t)]
      (when (seq more) (opaque! [:filter-arity]))
      (into [[:filter q]] (elab-source src depth)))
    :else (opaque! [:source (:op t) (when (= :perform (:op t)) (:datum (first (:args t))))])))

(defn elaborate
  "Elaborate the pipeline fn term under ctx {:resolve-def (fn [sym] ->
  {:term :value-id} or nil) :claim datum}. Returns {:fold {:f :init}
  :chain [[kind Expr] ..] :xs fvar-id :stages [kind ..] :performs #{op}},
  or throws ex-info carrying ::opaque."
  [ctx t]
  (when-not (= supported-claim (:claim ctx)) (opaque! [:claim (:claim ctx)]))
  (when-not (and (= :fn (:op t)) (= 1 (:arity t)) (not (:rest? t)))
    (opaque! [:not-a-unary-fn]))
  (let [body (:body t)
        env [{:type :list}]]
    (when-not (host-op? body :host/call 'clojure.core/reduce) (opaque! [:no-reduce]))
    (let [[_ & rargs] (:args body)
          [f init src] (case (count rargs)
                         3 rargs
                         2 (let [[f src] rargs
                                 p (host-var-prim f)]
                             (case p
                               + [f {:op :quote :datum 0} src]
                               * [f {:op :quote :datum 1} src]
                               (opaque! [:reduce-without-init p])))
                         (opaque! [:reduce-arity]))
          parsed (elab-source src 1)
          stage (fn [i kind thunk]
                  (try (thunk)
                       (catch clojure.lang.ExceptionInfo ex
                         (if-let [r (::opaque (ex-data ex))]
                           (opaque! [:opaque-stage i kind r])
                           (throw ex)))))
          F (stage (count parsed) :reduce #(elab-stage-fn ctx env f 2 :nat))
          I (stage (count parsed) :init #(want :nat (elab-expr ctx init env) :init))
          chain (vec (map-indexed
                      (fn [i [kind g]]
                        (let [i (- (count parsed) 1 i)] ; stage index from the source
                          [kind (stage i kind #(elab-stage-fn ctx env g 1 (if (= :map kind) :nat :bool)))]))
                      parsed))]
      {:fold {:f F :init I} :chain chain :xs (k/fvar!)
       :stages (conj (vec (reverse (map first parsed))) :reduce)
       :performs (into #{} (comp (filter #(= :perform (:op %))) (map :name))
                       (tree-seq (comp seq kc/children) kc/children t))})))

;; ---------------------------------------------------------------------------
;; fusion: the law-licensed rewrite, with its proof
;; ---------------------------------------------------------------------------

(defn beta
  "β-normalize a kernel term (the fragment is simply typed: terminates)."
  [x]
  (cond
    (e/app? x) (let [f (beta (e/app-fn x)) a (beta (e/app-arg x))]
                 (if (e/lam? f) (beta (e/instantiate1 (e/lam-body f) a)) (e/app f a)))
    (e/lam? x) (e/lam (e/lam-name x) (beta (e/lam-type x)) (beta (e/lam-body x)) :default)
    (e/forall? x) (e/forall' (e/forall-name x) (beta (e/forall-type x)) (beta (e/forall-body x)) :default)
    :else x))

(defn- list-expr [chain xs]
  (reduce (fn [l [kind g]] (if (= :map kind) (k/lmap Nat Nat g l) (k/lfilter Nat g l)))
          (e/fvar xs) (rseq chain)))

(defn- fold-expr [f init l] (k/foldl Nat Nat f init l))

(defn fuse
  "Rewrite foldl F I (stage_1 (.. (stage_n xs))) to one foldl over xs,
  absorbing the outermost stage at each step. Returns {:naive :fused (bodies
  over fvar xs) :goal :proof :laws}: proof : ∀ xs, naive = fused."
  [{:keys [fold chain xs]}]
  (let [I (:init fold)
        naive (fold-expr (:f fold) I (list-expr chain xs))
        steps (loop [F (:f fold) ch chain acc []]
                (if-let [[kind g] (first ch)]
                  (let [rest-l (list-expr (subvec ch 1) xs)
                        [ac x] [(k/fvar!) (k/fvar!)]
                        [law inst F']
                        (case kind
                          :map [k/law-map-name
                                (e/app* (k/c k/law-map-name) Nat Nat Nat F g rest-l I)
                                (beta (k/lam* [[ac "acc" Nat] [x "x" Nat]]
                                              (e/app* F (e/fvar ac) (e/app g (e/fvar x)))))]
                          :filter [k/law-filter-name
                                   (e/app* (k/c k/law-filter-name) Nat Nat F g rest-l I)
                                   (beta (k/lam* [[ac "acc" Nat] [x "x" Nat]]
                                                 (k/cond* Nat (e/app g (e/fvar x))
                                                          (e/app* F (e/fvar ac) (e/fvar x))
                                                          (e/fvar ac))))])]
                    (recur F' (subvec ch 1)
                           (conj acc {:law law :inst inst
                                      :to (fold-expr F' I rest-l)})))
                  acc))
        fused (if (seq steps) (:to (peek steps)) naive)
        chain-proof (if (empty? steps)
                      (e/app* (k/c "Eq.refl" [k/l1]) Nat naive)
                      (:proof
                       (reduce (fn [{:keys [proof to]} st]
                                 {:proof (e/app* (k/c "Eq.trans" [k/l1]) Nat naive to (:to st)
                                                 proof (:inst st))
                                  :to (:to st)})
                               {:proof (:inst (first steps)) :to (:to (first steps))}
                               (rest steps))))
        xsb [[xs "xs" (k/List Nat)]]]
    {:naive naive :fused fused
     :goal (k/pi* xsb (k/eq Nat naive fused))
     :proof (k/lam* xsb chain-proof)
     :laws (mapv :law steps)}))

;; ---------------------------------------------------------------------------
;; lowering: the fused ansatz term -> a host fn form
;; ---------------------------------------------------------------------------

(defn- lower-expr [x names]
  (let [[h args] (e/get-app-fn-args x)
        L #(lower-expr % names)]
    (cond
      (e/fvar? x) (or (names (e/fvar-id x)) (throw (ex-info "lower: free variable" {})))
      (e/lit-nat? x) (let [n (biginteger (e/lit-nat-val x))]
                       (if (<= (.bitLength n) 62) (long n)
                           (throw (ex-info "lower: literal beyond long" {:n n}))))
      (e/const? h)
      (let [n (nm/->string (e/const-name h))
            a #(L (nth args 0))
            b #(L (nth args 1))]
        (case n
          "Nat.add" (list 'Math/addExact (a) (b))
          "Nat.mul" (list 'Math/multiplyExact (a) (b))
          "Nat.succ" (list 'Math/incrementExact (a))
          "Nat.div" (list 'clojure.core/quot (a) (b))
          "Nat.mod" (list 'clojure.core/rem (a) (b))
          "Nat.beq" (list 'clojure.core/== (a) (b))
          "Nat.blt" (list 'clojure.core/< (a) (b))
          "Nat.ble" (list 'clojure.core/<= (a) (b))
          "Bool.not" (list 'clojure.core/not (a))
          "Bool.true" true
          "Bool.false" false
          "cond" (list 'if (L (nth args 1)) (L (nth args 2)) (L (nth args 3)))
          (throw (ex-info (str "lower: no lowering for " n) {:head n}))))
      :else (throw (ex-info "lower: unsupported term" {:term (str x)})))))

(defn- lower-form
  "The executable's host form. The step is a primitive long fn; every Nat
  operation is exact-or-throw; ArithmeticException declines (deopt)."
  [fused xs]
  (let [[h [_ _ F I src]] (e/get-app-fn-args fused)]
    (when-not (and (e/const? h) (= "List.foldl" (nm/->string (e/const-name h)))
                   (= (k/expr-data (e/fvar xs)) (k/expr-data src)))
      (throw (ex-info "lower: not a single foldl over the source" {})))
    (let [[ia ix] [(k/fvar!) (k/fvar!)]
          body (e/instantiate1 (e/lam-body (e/instantiate1 (e/lam-body F) (e/fvar ia))) (e/fvar ix))
          step (list 'fn (with-meta '[^long acc ^long x] {:tag 'long})
                     (lower-expr body {ia 'acc ix 'x}))]
      (list 'fn
            (list '[xs]
                  (list 'try
                        (list 'clojure.core/reduce step (lower-expr I {}) 'xs)
                        '(catch ArithmeticException _ klara.eval/deopt)))
            '([xs & _] klara.eval/deopt)))))

(defonce ^{:doc "form -> compiled host fn: the only producer of :run values"}
  compiled (atom {}))

(defn compile-form [form]
  (or (get @compiled form)
      (let [f (binding [*ns* (the-ns 'klara.fusion)] (eval form))]
        (get (swap! compiled #(if (contains? % form) % (assoc % form f))) form))))

;; ---------------------------------------------------------------------------
;; certificates (doc/01-core-v2 §11)
;; ---------------------------------------------------------------------------

(def side-conditions
  [{:condition :purity :status :by-construction
    :why "stages elaborate into ansatz terms; effects, host calls and opaque callees do not elaborate"}
   {:condition :input-is-list-nat :status :guarded :guard [:arg 0 :nat-list]}
   {:condition :reference-host-handlers :status :guarded
    :why "map/filter/reduce are :host/call performs; a dynamic handler could reinterpret them"}
   {:condition :nat-faithful-lowering :status :checked-at-runtime
    :why "exact-or-throw arithmetic; ArithmeticException -> deopt to generic"}
   {:condition :overflow-coincidence :status :trusted
    :why "fusion is operation-preserving: both paths perform the same arithmetic on the same values"}])

(defn- form-hash [form] (kc/sha256 (binding [*print-meta* false] (pr-str form))))

(defn- build
  "Elaborate, fuse and lower from a source record. Throws ::opaque."
  [{:keys [term stages claim]}]
  (let [ctx {:resolve-def (fn [sym] (get stages sym)) :claim claim}
        el (elaborate ctx term)
        fu (fuse el)]
    (assoc fu :elab el :form (lower-form (:fused fu) (:xs el)))))

(defn- certificate [code-id guards source {:keys [goal proof laws form]}]
  (let [{:keys [env cohort] :as ps} (k/proof-env)
        cert {:code-id code-id
              :assumptions (set guards)
              :checker :ansatz/kernel
              :checker-version (str @k/checker-version "+" elaborator-version)
              :provenance {:specializer ::optimize :elaborator elaborator-version
                           :source-term-id (kc/code-id (:term source))}
              :source (update source :stages
                              #(into (sorted-map) (map (fn [[sy dep]] [sy (select-keys dep [:term :value-id])])) %))
              :laws (into (sorted-map) (map (fn [l] [l (get-in ps [:laws l])])) (distinct laws))
              :theorem {:name (str "Klara.fusion." (subs (k/expr-hash goal) 0 16))
                        :goal-hash (k/expr-hash goal)
                        :proof-hash (k/expr-hash proof)}
              :lowering {:form-hash (form-hash form)}
              :side-conditions side-conditions
              :cohort cohort
              :closure (k/closure env [goal proof])
              :payload {:goal goal :proof proof}}]
    (assoc cert :digest (s/digest cert))))

(defn check
  "The :ansatz/kernel checker: nil if exe's certificate genuinely
  certifies it, else a reason. Recomputes everything it can from the
  recorded source and rechecks the supplied proof in the kernel."
  [{:keys [code-id guards certificate form run]}]
  (let [{:keys [env cohort laws] :as ps} (k/proof-env)
        {:keys [source theorem payload] :as cert} certificate
        gs (set guards)]
    (cond
      (not= (:checker-version cert) (str @k/checker-version "+" elaborator-version))
      :checker-version-mismatch

      (not= (:cohort cert) cohort) :cohort-mismatch

      (some (fn [[l h]] (not= h (get laws l))) (:laws cert)) :law-mismatch

      (not= code-id (kc/code-id (:term source))) :source-mismatch

      (some (fn [[sy {:keys [term value-id]}]]
              (or (not= value-id (kc/code-id term)) (not (gs [:world sy value-id]))))
            (:stages source))
      :stage-mismatch

      (not (and (gs [:arg 0 :nat-list]) (gs [:captures []])
                (some #(= :unhandled (first %)) gs)))
      :missing-guard

      :else
      (let [b (try (build source)
                   (catch clojure.lang.ExceptionInfo ex
                     (if (::opaque (ex-data ex)) ::opaque (throw ex))))]
        (cond
          (= ::opaque b) :source-does-not-elaborate
          (not (gs [:unhandled (:performs (:elab b))])) :missing-guard
          (not= (k/expr-hash (:goal b)) (:goal-hash theorem)) :goal-mismatch
          (not= (k/expr-hash (:proof payload)) (:proof-hash theorem)) :proof-hash-mismatch
          (not= (k/expr-hash (:goal payload)) (:goal-hash theorem)) :goal-mismatch
          (not= (:closure cert) (k/closure env [(:goal b) (:proof payload)])) :closure-mismatch
          (not (k/verifies? env (:goal b) (:proof payload))) :proof-rejected
          (not= form (:form b)) :lowering-mismatch
          (not= (form-hash form) (:form-hash (:lowering cert))) :lowering-mismatch
          (not (identical? run (get @compiled form))) :lowering-mismatch)))))

(s/register-checker! :ansatz/kernel check)

;; ---------------------------------------------------------------------------
;; the front door
;; ---------------------------------------------------------------------------

(defn session "A world and a specialization cache." []
  {:world (w/make-world) :cache (s/make-cache)})

(defn define! [{:keys [world]} form] (d/define! world form))

(defn claim!
  "Publish a shape claim for sym (only (List Nat) -> Nat is supported)."
  [sess sym shape]
  (define! sess (list 'def (claim-sym sym) (list 'quote shape))))

(defn- world-resolver [root reads]
  (fn [sym]
    (let [e (w/entry* root sym)]
      (when (and e (= :def (:kind e)) (not (w/pending? root e)))
        (let [dep {:term (:code e) :value-id (:value-id e)}]
          (vswap! reads assoc sym dep)
          dep)))))

(defn specialize
  "Build a certified fused executable for world function sym in root, or
  {:status :generic :reason ..}."
  [root sym]
  (let [f (d/lookup root sym)
        term (ev/closure-term f)
        reads (volatile! {})
        resolve-def (world-resolver root reads)
        claim (some-> (resolve-def (claim-sym sym)) :term :datum)]
    (if-not claim
      {:status :generic :reason :no-shape-claim}
      (try
        (let [_ (elaborate {:resolve-def resolve-def :claim claim} term) ; records reads
              source {:term term :stages @reads :claim claim}
              b (build source)
              code-id (kc/code-id term)
              guards (-> (s/world-guards term root)
                         (into (map (fn [[sy {:keys [value-id]}]] [:world sy value-id])) @reads)
                         (conj [:captures (ev/closure-locals f)] [:arg 0 :nat-list]
                               [:unhandled (:performs (:elab b))]))
              cert (certificate code-id guards source b)]
          {:status :fused
           :stages (:stages (:elab b))
           :laws (:laws b)
           :theorem (get-in cert [:theorem :name])
           :executable {:code-id code-id :guards guards :form (:form b)
                        :run (compile-form (:form b)) :deopts (atom 0)
                        :certificate cert}})
        (catch clojure.lang.ExceptionInfo ex
          (if-let [r (::opaque (ex-data ex))]
            {:status :generic :reason r}
            (throw ex)))))))

(defn optimize!
  "Specialize sym in the session's current root and install the
  executable (install rechecks the certificate). Returns a report."
  [{:keys [world cache]} sym]
  (let [r (specialize (w/snapshot world) sym)]
    (if (= :fused (:status r))
      (do (s/install! cache (:executable r))
          (-> r (dissoc :executable)
              (assoc :code-id (get-in r [:executable :code-id])
                     :guards (get-in r [:executable :guards]))))
      r)))

(defn run
  "Evaluate form in the session's current root with the cache active."
  [{:keys [world cache]} form]
  (s/with-cache cache (d/eval-form (w/snapshot world) form)))

(defn run-generic
  "Evaluate form with no cache (the reference result)."
  [{:keys [world]} form]
  (d/eval-form (w/snapshot world) form))
