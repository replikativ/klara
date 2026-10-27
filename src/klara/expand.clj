(ns klara.expand
  "The expander: surface forms -> Klara Core terms (klara.core), ported
  from v0.expand + v0.macros (experiment X1).

  Syntax is plain Clojure data; identifiers carry a ::scopes set in
  METADATA (= and hash ignore it, so datum equality is untouched).

  Hygiene (scope sets, simplified as in v0):
    - binders add a fresh scope to their binder ids and region;
    - a binding registers (name, scope-set) -> rename;
    - a reference resolves to the binding whose scope set is the LARGEST
      SUBSET of its own; incomparable maxima are an ambiguity error;
    - macro calls use the FLIP discipline: flip a fresh intro scope on
      the input and on the output, so macro-introduced identifiers can
      neither capture nor be captured.

  Output is core terms. The lexical environment is a vector of renames;
  a resolved rename becomes a de Bruijn index, so terms carry no names
  and the CodeId (klara.core/code-id) is α-canonical by construction.

  The world (klara.world) is the macro environment. Every free
  identifier is looked up in the expansion BASIS through the recording
  reader: [:macro s h], [:def s], and — the gap X1 left — NEGATIVE
  lookups [:absent s], so that later defining s (as a function or a
  macro) re-expands the forms that fell back past it. Transformers are
  world values run by T0 under the expansion basis; the world values
  they consume are recorded as [:value s h].

  Free identifiers that the world does not define fall back, in order, to
  the built-in qq macro, Tier L prims (operator position), clojure.core
  host macros (compat path, with the flip discipline), and clojure.core
  host functions via the ambient :host/call and :host/var effects.
  Linked Clojure is outside the basis guarantees (doc/01-core-v1 Q12).

  Surface forms beyond Clojure's: (handle [h {:op f .. :return r}] body..),
  (handle :dynamic {:exn/raise f ..} body..), (perform h :op args..),
  (perform :ns/op args..), (prim op args..), (specialize f args..)."
  (:require [clojure.set :as set]
            [klara.core :as c]
            [klara.world :as w]
            [klara.eval :as ev]))

;; ---------------------------------------------------------------------------
;; scopes on metadata (v0)
;; ---------------------------------------------------------------------------

(defn scopes [x] (or (::scopes (meta x)) #{}))

(defn- update-scopes [x f sc]
  (if (symbol? x) (vary-meta x update ::scopes (fnil f #{}) sc) x))

(defn- walk-form [form f]
  (cond
    (symbol? form) (f form)
    (seq? form)    (if (= 'quote (first form))
                     form
                     (with-meta (apply list (map #(walk-form % f) form)) (meta form)))
    (vector? form) (with-meta (mapv #(walk-form % f) form) (meta form))
    (map? form)    (with-meta (into {} (map (fn [[k v]] [(walk-form k f) (walk-form v f)]) form))
                     (meta form))
    (set? form)    (with-meta (into #{} (map #(walk-form % f) form)) (meta form))
    :else form))

(defn add-scope [form sc] (walk-form form #(update-scopes % conj sc)))
(defn flip-scope [form sc]
  (walk-form form #(update-scopes % (fn [ss s] (if (contains? ss s) (disj ss s) (conj ss s))) sc)))

(defn strip
  "Datum of a syntax form: scopes removed everywhere (also under quote)."
  [form]
  (cond
    (symbol? form) (with-meta form (not-empty (dissoc (meta form) ::scopes)))
    (seq? form)    (apply list (map strip form))
    (vector? form) (mapv strip form)
    (map? form)    (into {} (map (fn [[k v]] [(strip k) (strip v)]) form))
    (set? form)    (into #{} (map strip form))
    :else form))

;; ---------------------------------------------------------------------------
;; qq — the non-qualifying quasiquote (v0): bare symbols stay bare
;; ---------------------------------------------------------------------------

(defn- unquote? [x] (and (seq? x) (= 'clojure.core/unquote (first x))))
(defn- splice? [x] (and (seq? x) (= 'clojure.core/unquote-splicing (first x))))

(defn qq-build [form]
  (let [parts (fn [form]
                (cons 'clojure.core/concat
                      (map (fn [el] (if (splice? el) (second el)
                                        (list 'clojure.core/list (qq-build el))))
                           form)))]
    (cond
      (unquote? form) (second form)
      (seq? form) (if (some splice? form)
                    (list 'clojure.core/apply 'clojure.core/list (parts form))
                    (cons 'clojure.core/list (map qq-build form)))
      (vector? form) (if (some splice? form)
                       (list 'clojure.core/vec (parts form))
                       (cons 'clojure.core/vector (map qq-build form)))
      (map? form) (cons 'clojure.core/hash-map
                        (mapcat (fn [[k v]] [(qq-build k) (qq-build v)]) form))
      (symbol? form) (list 'quote form)
      :else form)))

(def builtin-macros {'qq (fn [[_ template]] (qq-build template))})

;; ---------------------------------------------------------------------------
;; context: one per expansion session
;; ---------------------------------------------------------------------------

(def ^:dynamic *memo*
  "nil, or {:key (fn [ctx env form]) :table atom}: a sub-expansion cache
  over macro call sites. Its key function decides soundness."
  nil)

(def expansions "Work counter: top-level expansions (expand-recorded)." (atom 0))

(defn new-ctx
  "ctx: scope counter, binding table, provenance log; :basis is the root
  the expansion reads, :self the name being defined (if any)."
  ([] (new-ctx w/empty-root))
  ([basis]
   {:counter (atom 0) :bindings (atom {}) :log (atom []) :basis basis :self nil}))

(defn fresh-scope! [ctx] (swap! (:counter ctx) inc))
(defn- observe! [ctx event] (swap! (:log ctx) conj event))

(defn- bind! [ctx id rename]
  (swap! (:bindings ctx) assoc-in [(with-meta id nil) (scopes id)] rename))

(defn resolve-id
  "Largest-subset resolution to a rename, or nil when free."
  [ctx id]
  (let [cands (get @(:bindings ctx) (with-meta id nil))
        applicable (filter (fn [[ss _]] (set/subset? ss (scopes id))) cands)]
    (when (seq applicable)
      (let [maximal (filter (fn [[ss _]]
                              (not-any? (fn [[ss2 _]] (and (not= ss ss2) (set/subset? ss ss2)))
                                        applicable))
                            applicable)]
        (if (= 1 (count maximal))
          (val (first maximal))
          (throw (ex-info "expand: ambiguous identifier (incomparable scope sets)"
                          {:id id :candidates (map key maximal)})))))))

;; env: {:locals [rename ..] :recur rename|nil}
(def empty-env {:locals [] :recur nil})

(defn- local-term [env r]
  (let [ls (:locals env) i (.lastIndexOf ^java.util.List ls r)]
    (when (neg? i) (throw (ex-info "expand: binding not in lexical scope" {:rename r})))
    (c/local (- (count ls) 1 i))))

(defn- push-local [env r] (update env :locals conj r))

(defn- bind-local
  "Bind identifier id (already scoped) to a fresh rename: [env' rename]."
  [ctx env id]
  (let [r (gensym (name id))]
    (bind! ctx id r)
    [(push-local env r) r]))

;; ---------------------------------------------------------------------------
;; free identifiers: world (recorded), then built-ins and host
;; ---------------------------------------------------------------------------

(defn- world-entry [ctx bare]
  (when-not (= bare (:self ctx))
    (w/entry (:basis ctx) bare :exists)))

(defn- host-var [sym]
  (let [v (if (qualified-symbol? sym)
            (try (requiring-resolve sym) (catch Exception _ nil))
            (ns-resolve (the-ns 'clojure.core) sym))]
    (when (var? v) v)))

(defn- host-macro [sym] (when-let [v (host-var sym)] (when (:macro (meta v)) v)))
(defn- host-fn [sym] (when-let [v (host-var sym)] (when-not (:macro (meta v)) (symbol v))))

(defn- unbound! [bare]
  (throw (ex-info (str "expand: unable to resolve " bare) {:sym bare})))

(defn- free-ref
  "A free identifier in value position."
  [ctx bare]
  (cond
    (qualified-symbol? bare)
    (cond
      (host-fn bare) (c/perform nil :host/var (c/quote* (host-fn bare)))
      (class? (resolve (symbol (namespace bare))))
      (c/perform nil :host/static-field (c/quote* (symbol (namespace bare)))
                 (c/quote* (symbol (name bare))))
      :else (unbound! bare))

    (= bare (:self ctx)) (c/resolve* bare)

    :else
    (let [e (world-entry ctx bare)]
      (cond
        (= :def (:kind e)) (c/resolve* bare)
        (= :macro (:kind e)) (throw (ex-info (str "expand: macro " bare " used as value")
                                             {:sym bare}))
        :else (if-let [q (host-fn bare)]
                (c/perform nil :host/var (c/quote* q))
                (unbound! bare))))))

;; ---------------------------------------------------------------------------
;; the expander
;; ---------------------------------------------------------------------------

(declare expand)

(defn- expand-body
  "Implicit do: (let [_ f1] (let [_ f2] .. fn)) with hidden binders."
  [forms ctx env]
  (cond
    (empty? forms) (c/quote* nil)
    (empty? (rest forms)) (expand (first forms) ctx env)
    :else (c/let1 (expand (first forms) ctx env)
                  (expand-body (rest forms) ctx (push-local env (gensym "_"))))))

(defn- wrap-lets [inits body]
  (reduce (fn [b init] (c/let1 init b)) body (reverse inits)))

(defn- expand-bindings
  "Sequential let* discipline: one fresh scope per pair; the value is
  expanded BEFORE its binder's scope exists. Returns
  [inits env' body' binders' renames]."
  [bindings body ctx env]
  (loop [pairs (partition 2 bindings) body (vec body) env env inits [] xs [] rs []]
    (if (empty? pairs)
      [inits env body xs rs]
      (let [[x v] (first pairs)
            v' (expand v ctx env)
            sc (fresh-scope! ctx)
            x' (add-scope x sc)
            [env' r] (bind-local ctx env x')]
        (recur (map (fn [[a b]] [(add-scope a sc) (add-scope b sc)]) (rest pairs))
               (mapv #(add-scope % sc) body)
               env' (conj inits v') (conj xs x') (conj rs r))))))

(defn- expand-let* [[_ bindings & body] ctx env]
  (let [[inits env' body'] (expand-bindings bindings body ctx env)]
    (wrap-lets inits (expand-body body' ctx (assoc env' :recur nil)))))

(defn- expand-lambda
  "One parameter scope; supports & rest. recur-r is the recur target."
  [params body ctx env recur-r]
  (let [sc (fresh-scope! ctx)
        [fixed [_ rest-p]] (split-with #(not= '& %) params)
        ps (cond-> (vec fixed) rest-p (conj rest-p))
        env' (reduce (fn [e p] (first (bind-local ctx e (add-scope p sc)))) env ps)
        body' (map #(add-scope % sc) body)]
    (c/lam (count fixed) (boolean rest-p)
           (expand-body body' ctx (assoc env' :recur recur-r)))))

(defn- has-recur?
  "Conservative scan for recur outside nested fn*/loop* forms."
  [form]
  (cond
    (= 'recur form) true
    (seq? form) (and (not (contains? '#{quote fn* loop* fn loop clojure.core/fn
                                        clojure.core/loop} (first form)))
                     (boolean (some has-recur? form)))
    (coll? form) (boolean (some has-recur? form))
    :else false))

(defn- expand-fn* [[_ & tail] ctx env]
  (let [[fname tail] (if (symbol? (first tail)) [(first tail) (rest tail)] [nil tail])
        arities (if (vector? (first tail)) [tail] tail)
        _ (when (not= 1 (count arities))
            (throw (ex-info "expand: S1 supports single-arity fns only" {:form tail})))
        [params & body] (first arities)]
    (if (or fname (has-recur? body))
      (let [sc (fresh-scope! ctx)
            self (when fname (add-scope fname sc))
            r (gensym (if fname (name fname) "recur"))
            _ (when self (bind! ctx self r))
            body (if fname (map #(add-scope % sc) body) body)
            params (if fname (add-scope params sc) params)]
        (c/letrec [(expand-lambda params body ctx (push-local env r) r)] (c/local 0)))
      (expand-lambda params body ctx env nil))))

(defn- expand-loop* [[_ bindings & body] ctx env]
  (let [[inits env1 body' xs rs] (expand-bindings bindings body ctx env)
        lp (gensym "loop")
        env2 (push-local env1 lp)
        lam (expand-lambda xs body' ctx env2 lp)]
    (wrap-lets inits
               (c/letrec [lam] (apply c/app (c/local 0) (map #(local-term env2 %) rs))))))

(defn- strip-fn-name [f]
  (if (and (seq? f) (contains? '#{fn* fn clojure.core/fn} (first f)) (symbol? (second f)))
    (apply list (first f) (drop 2 f))
    f))

(defn- expand-letfn* [[_ bindings & body] ctx env]
  (let [sc (fresh-scope! ctx)
        pairs (partition 2 bindings)
        env' (reduce (fn [e [f _]] (first (bind-local ctx e (add-scope f sc)))) env pairs)
        inits (mapv (fn [[_ v]] (expand (add-scope (strip-fn-name v) sc) ctx env')) pairs)]
    (when-not (every? #(= :fn (:op %)) inits)
      (throw (ex-info "expand: letfn* inits must be plain fns" {:form bindings})))
    (c/letrec inits (expand-body (map #(add-scope % sc) body) ctx env'))))

(def ^:private catch-all '#{Throwable Exception Object java.lang.Throwable
                            java.lang.Exception java.lang.Object :default})

(defn- expand-try
  "(try body.. (catch Cls e h..)..) => a dynamic handler for :exn/raise
  whose clause tests the classes in order and re-raises otherwise."
  [[_ & forms] ctx env]
  (let [clause? (fn [f] (and (seq? f) (contains? '#{catch finally} (first f))))
        [body clauses] (split-with (complement clause?) forms)
        _ (when (some #(= 'finally (first %)) clauses)
            (throw (ex-info "expand: finally is not in S1" {})))
        ex-r (gensym "ex") k-r (gensym "k")
        cenv (-> env (push-local ex-r) (push-local k-r) (assoc :recur nil))
        ex (local-term cenv ex-r)
        clause-body
        (reduce (fn [else [_ cls e & cbody]]
                  (let [sc (fresh-scope! ctx)
                        [cenv' _] (bind-local ctx cenv (add-scope e sc))
                        handler (c/let1 ex (expand-body (map #(add-scope % sc) cbody) ctx cenv'))
                        test (if (contains? catch-all cls)
                               (c/quote* true)
                               (c/perform nil :host/call (c/quote* 'clojure.core/instance?)
                                          (c/perform nil :host/class (c/quote* cls)) ex))]
                    (c/if* test handler else)))
                (c/perform nil :exn/raise ex)
                (reverse clauses))]
    (c/handle :dynamic {:exn/raise (c/lam 2 clause-body)}
              (expand-body body ctx (push-local env (gensym "inst"))))))

(defn- expand-handle [[_ spec & more] ctx env]
  (let [[mode h cmap body] (if (vector? spec)
                             [:lexical (first spec) (second spec) more]
                             [:dynamic nil (first more) (rest more)])
        clauses (into {} (map (fn [[k v]] [k (expand v ctx env)])) (dissoc cmap :return))
        ret (some-> (:return cmap) (expand ctx env))]
    (if h
      (let [sc (fresh-scope! ctx)
            [env' _] (bind-local ctx env (add-scope h sc))]
        (c/handle mode clauses ret (expand-body (map #(add-scope % sc) body) ctx env')))
      (c/handle mode clauses ret (expand-body body ctx (push-local env (gensym "inst")))))))

(defn- expand-perform [[_ a & more] ctx env]
  (if (c/ambient? a)
    (apply c/perform nil a (map #(expand % ctx env) more))
    (let [[op & args] more]
      (apply c/perform (expand a ctx env) op (map #(expand % ctx env) args)))))

(def special-forms
  '#{quote if do let* loop* recur fn* letfn* throw try handle perform prim
     specialize def})

(defn- expand-special [bare form ctx env]
  (let [ex #(expand % ctx env)]
    (case bare
      quote (c/quote* (strip (second form)))
      if (let [[_ t a b] form] (c/if* (ex t) (ex a) (ex b)))
      do (expand-body (rest form) ctx env)
      let* (expand-let* form ctx env)
      loop* (expand-loop* form ctx env)
      recur (if-let [r (:recur env)]
              (apply c/app (local-term env r) (map ex (rest form)))
              (throw (ex-info "expand: recur outside a recur target" {:form form})))
      fn* (expand-fn* form ctx env)
      letfn* (expand-letfn* form ctx env)
      throw (c/perform nil :exn/raise (ex (second form)))
      try (expand-try form ctx env)
      handle (expand-handle form ctx env)
      perform (expand-perform form ctx env)
      prim (apply c/prim (second form) (map ex (drop 2 form)))
      specialize (apply c/specialize (map ex (rest form)))
      def (throw (ex-info "expand: def is only allowed at top level" {:form form})))))

;; ---------------------------------------------------------------------------
;; macro calls (flip discipline) with the optional sub-expansion memo
;; ---------------------------------------------------------------------------

(defn- call-macro [f mname form ctx env]
  (let [k (when *memo* ((:key *memo*) ctx env form))
        hit (when k (find @(:table *memo*) k))]
    (if hit
      (let [[term reads] (val hit)]
        (doseq [r reads] (w/note-read! r))
        term)
      (let [intro (fresh-scope! ctx)
            out (flip-scope (f (flip-scope form intro)) intro)
            _ (observe! ctx {:event :macro :macro mname :in form :out out})
            reads (atom #{})
            term (binding [w/*reads* (if w/*reads* reads nil)] (expand out ctx env))]
        (when w/*reads* (swap! w/*reads* into @reads))
        (when k (swap! (:table *memo*) assoc k [term @reads]))
        term))))

(defn world-transformer
  "The calling convention of a world macro: call form -> output form, the
  transformer running in T0 under the expansion basis."
  [e basis]
  (let [f (ev/rebase (:value e) basis)]
    (fn [call] (ev/call-value f (vec (rest call))))))

(defn- host-transformer [v]
  (fn [call] (apply @v call nil (rest call))))

(defn- expand-app [form ctx env]
  (c/app* (expand (first form) ctx env) (mapv #(expand % ctx env) (rest form))))

(defn- expand-seq [form ctx env]
  (let [head (first form)
        bare (when (symbol? head) (with-meta head nil))
        args #(mapv (fn [a] (expand a ctx env)) (rest form))]
    (cond
      (nil? bare) (expand-app form ctx env)
      (contains? special-forms bare) (expand-special bare form ctx env)
      (resolve-id ctx head) (expand-app form ctx env)
      (qualified-symbol? bare)
      (if-let [v (host-macro bare)]
        (call-macro (host-transformer v) bare form ctx env)
        (cond
          (host-fn bare) (apply c/perform nil :host/call (c/quote* (host-fn bare)) (args))
          (class? (resolve (symbol (namespace bare))))
          (apply c/perform nil :host/static (c/quote* (symbol (namespace bare)))
                 (c/quote* (symbol (name bare))) (args))
          :else (unbound! bare)))
      (= bare (:self ctx)) (expand-app form ctx env)
      :else
      (let [e (world-entry ctx bare)]
        (case (:kind e)
          :macro (call-macro (world-transformer e (:basis ctx)) bare form ctx env)
          :def (expand-app form ctx env)
          (cond
            (builtin-macros bare) (call-macro (builtin-macros bare) bare form ctx env)
            (c/prims bare) (apply c/prim bare (args))
            (host-macro bare) (call-macro (host-transformer (host-macro bare)) bare form ctx env)
            (host-fn bare) (apply c/perform nil :host/call (c/quote* (host-fn bare)) (args))
            :else (unbound! bare)))))))

(defn- constant? [form]
  (not-any? #(or (symbol? %) (seq? %)) (tree-seq coll? seq form)))

(defn expand
  "Expand syntax form under ctx and lexical env into a core term."
  [form ctx env]
  (cond
    (symbol? form) (if-let [r (resolve-id ctx form)]
                     (local-term env r)
                     (free-ref ctx (with-meta form nil)))
    (seq? form) (if (empty? form) (c/quote* ()) (expand-seq form ctx env))
    (and (coll? form) (constant? form)) (c/quote* (strip form))
    (vector? form) (apply c/prim 'vector (map #(expand % ctx env) form))
    (map? form) (apply c/prim 'hash-map (mapcat (fn [[k v]] [(expand k ctx env) (expand v ctx env)]) form))
    (set? form) (apply c/prim 'hash-set (map #(expand % ctx env) form))
    :else (c/quote* form)))

;; ---------------------------------------------------------------------------
;; top level: def / defmacro / expression, with recorded reads
;; ---------------------------------------------------------------------------

(defn- top-macro
  "If form is a macro call at top level, its transformer (world or host)."
  [form ctx]
  (when (and (seq? form) (symbol? (first form)))
    (let [bare (with-meta (first form) nil)]
      (when-not (or (contains? special-forms bare) (= 'defmacro bare))
        (if (qualified-symbol? bare)
          (some-> (host-macro bare) host-transformer)
          (let [e (world-entry ctx bare)]
            (case (:kind e)
              :macro (world-transformer e (:basis ctx))
              :def nil
              (some-> (host-macro bare) host-transformer))))))))

(defn expand-recorded
  "Expand a top-level form against basis root. Returns
  {:kind :def|:macro|:expr :name sym :term core :code-id h :reads #{..}}.
  (def n e) defines a value, (defmacro n [ps] body..) a transformer
  (the code of (fn* [ps] body..)); top-level macro calls are expanded
  until one of these appears."
  ([form root] (expand-recorded form root (new-ctx root)))
  ([form root ctx]
   (swap! expansions inc)
   (let [ctx (assoc ctx :basis root)
         reads (atom #{})]
     (binding [w/*reads* reads]
       (let [res (loop [form form]
                   (let [head (when (and (seq? form) (symbol? (first form)))
                                (with-meta (first form) nil))]
                     (cond
                       (= 'def head)
                       (let [[_ nm init] form nm (with-meta nm nil)]
                         {:kind :def :name nm
                          :term (expand init (assoc ctx :self nm) empty-env)})
                       (= 'defmacro head)
                       (let [[_ nm params & body] form nm (with-meta nm nil)]
                         {:kind :macro :name nm
                          :term (expand (apply list 'fn* (vec params) body)
                                        (assoc ctx :self nm) empty-env)})
                       :else
                       (if-let [t (top-macro form ctx)]
                         (let [intro (fresh-scope! ctx)]
                           (recur (flip-scope (t (flip-scope form intro)) intro)))
                         {:kind :expr :term (expand form ctx empty-env)}))))]
         (c/assert-wf! (:term res))
         (assoc res :code-id (c/code-id (:term res))
                :reads (into #{} (remove #(= (:name res) (second %))) @reads)))))))

(defn expand-expr
  "Expression form -> core term under basis root (reads discarded)."
  [form root]
  (:term (expand-recorded form root)))

;; ---------------------------------------------------------------------------
;; sub-expansion cache keys (X1 pass criterion v)
;; ---------------------------------------------------------------------------

(defn form-key
  "The naive key: the form itself. Scopes live in metadata, which = and
  hash ignore, so identifiers resolving to different binders collide."
  [_ctx _env form]
  form)

(defn alpha-key
  "Binding-qualified key: every identifier is replaced by what it
  resolves to HERE — its de Bruijn index when local, its bare name when
  free. The core term of a macro call depends only on the form, these
  resolutions and the world reads (replayed on hit), so equal keys give
  equal terms: closed forms share, and shadowing cannot collide."
  [ctx env form]
  (c/sha256
   (pr-str
    (letfn [(walk [f]
              (cond
                (symbol? f) (if-let [r (resolve-id ctx f)]
                              [:l (:index (local-term env r))]
                              [:f (with-meta f nil)])
                (seq? f) (if (= 'quote (first f)) [:q (strip f)] (mapv walk f))
                (vector? f) [:vec (mapv walk f)]
                (map? f) [:map (sort-by pr-str (map #(mapv walk %) f))]
                (set? f) [:set (sort-by pr-str (map walk f))]
                :else f))]
      (walk form)))))

(defn with-memo*
  "Run thunk with the sub-expansion cache keyed by key-fn: [result table]."
  [key-fn thunk]
  (let [table (atom {})]
    [(binding [*memo* {:key key-fn :table table}] (thunk)) @table]))
