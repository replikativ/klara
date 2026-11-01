(ns klara.compile.lower
  "The backend (spec/L4-compiler.md#lowering): checked Core terms to JVM
  classes through the Clojure compiler.

  A lowered function is a host fn. Late links are looked up in the effective
  world of the call (L4.lower.links), read from the machine's current
  context. Each lowering is compiled by `eval`, which uses a fresh class
  loader (L4.retain.classes).

  Leaving compiled code (L4.exec.frame-state). The candidate is put in
  A-normal form (klara.compile.anf) and prepared like any term
  (klara.runtime.prepare). Lowering walks the term and its prepared nodes
  together, so at every point where compiled code may leave it knows the
  interpreter node to continue at, which compiled locals fill which
  environment slots, and the `let` frames around the point. It leaves by
  throwing a Leave that carries this state:

  - a failed speculation, `(if guard specialized reference)`, continues at
    the reference node (L4.exec.leave);
  - a callee that performs an effect, or whose budget runs out, in a nested
    machine: the nested machine's state is carried along;
  - the budget running out at a function entry: the call is applied again by
    the interpreter.

  Each compiled call site in a non-tail position adds its own frames as the
  Leave passes through, so the receiving executable rebuilds the whole
  continuation and the machine goes on from there: nothing is re-executed."
  (:require [klara.compile.anf :as anf]
            [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.prepare :as prep]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Leaving

(defn leave?
  "The leave state carried by exception `e`, or nil."
  [e]
  (when (instance? clojure.lang.ExceptionInfo e) (::leave (ex-data e))))

(defn- leave!
  "Leave compiled code: `state` is one of
     {:mode :eval :node n :env env}      continue at node n
     {:mode :apply :f f :args args}      apply f to args
     {:mode :nested :state st}           continue a nested machine's state
   `frames` are the let frames around the leaving point, innermost first."
  [state frames]
  (throw (ex-info "leave compiled code" {::leave (volatile! (assoc state :frames frames))})))

(defn push-frames!
  "A Leave passing through a compiled call site: add the site's frames
   (outside the frames already collected) and pass it on."
  [e frames]
  (when-let [l (leave? e)]
    (vswap! l update :frames into frames))
  (throw e))

(defn leave-eval! [node env frames] (leave! {:mode :eval :node node :env env} frames))

(defn let-frame [body-node env] {:f :let :body body-node :env env})

;; Stress testing: leave at function entries with probability `stress`, to
;; exercise frame states everywhere (as V8's --deopt-every-n-times does).
(defonce stress (atom nil))

(defn tick!
  "L4.lower.steps: one step per function entry and loop iteration. True when
   compiled code must leave here: the budget ran out, or stress testing."
  []
  (let [^objects c (m/current-context)
        ^longs meter (:meter (aget c 2))]
    (or (when meter
          (aset meter 0 (dec (aget meter 0)))
          (neg? (aget meter 0)))
        (when-let [p @stress] (< (Math/random) (double p))))))

(defn interpreted
  "The interpreter's closure for a compiled function: its node and captured values."
  [fn-node captured]
  (Closure. (.-term ^klara.runtime.prepare.Fn fn-node) fn-node captured nil))

(defn leave-apply!
  "Leave at a function entry: the interpreter applies the function again."
  [fn-node captured args]
  (leave! {:mode :apply :f (interpreted fn-node captured) :args args} []))

(defn resume
  "The machine state that continues `st`, the state in which an executable
   was entered, after compiled code left with `leave` (L4.exec.frame-state)."
  [st leave]
  (let [{:keys [mode frames]} leave
        k (reduce conj (:k st) (rseq (vec frames)))]
    (case mode
      :eval (assoc st :mode :eval :ctl (:node leave) :env (:env leave) :k k)
      :apply (assoc st :mode :apply :ctl [(:f leave) (vec (:args leave)) nil] :env nil :k k)
      :nested (let [n (:state leave)
                    inner (take-while #(not= :boundary (:f %)) (:k n))]
                (assoc st :mode (:mode n) :ctl (:ctl n) :env (:env n)
                       :k (reduce conj k (reverse inner)) :world (:world n) :mint (:mint n))))))

;; ---------------------------------------------------------------------------
;; Calls

;; A call site of a late link: the world id, dispatch epoch and value of its
;; last resolution, as in the interpreter's globals (klara.runtime.prepare).
(definterface ISite (lookup [q]))

(deftype Site [^:volatile-mutable entry]
  ISite
  (lookup [_ q]
    (let [^objects c (m/current-context)
          world (aget c 0)
          id (.-id ^klara.runtime.value.World world)
          epoch (.get m/dispatch-epoch)]
      (or (klara.runtime.prepare/entry-value entry id epoch)
          (let [x (m/resolve-link {:kind :late :name q} world (:session (aget c 2)))]
            (set! entry (klara.runtime.prepare.CacheEntry. id epoch x))
            x)))))

(defn late [^ISite site q] (.lookup site q))

(defn- nested
  "Run a Klara function in a nested machine. If it performs an effect it
   does not handle, or its budget runs out, its state leaves with it."
  [f args]
  (let [^objects c (m/current-context)]
    (try (m/call-in [(aget c 0) (aget c 1) (aget c 2)] f args true)
         (catch clojure.lang.ExceptionInfo e
           (if-let [st (::m/state (ex-data e))]
             (leave! {:mode :nested :state st} [])
             (throw e))))))

(defn call
  "Call any function value from compiled code (L4.lower.calls): compiled
   callees directly, Klara closures in a nested machine, host functions as
   they are."
  [f args]
  (cond
    (instance? klara.runtime.value.IExecutable f)
    (let [^objects c (m/current-context)
          r (v/-call f (aget c 0) (aget c 1) (aget c 2) args)]
      (if (identical? r v/fallback) (nested f args) r))
    (or (instance? Closure f) (instance? klara.runtime.value.Continuation f) (m/intrinsic? f))
    (nested f args)
    ;; the same rule as the interpreter (L0.eval.not-fn)
    (not (instance? clojure.lang.IFn f))
    (fail :L0.eval.not-fn (str "cannot call " (pr-str f) ": not a function") :value (pr-str f))
    :else (apply f args)))

;; ---------------------------------------------------------------------------
;; Lowering

(def ^:private unsupported #{:try :interop :code :hole :def :letrec})

(defn- link-value [link]
  (case (:kind link)
    :pinned (klara.runtime.world/pin (:world link) (:name link))
    :guarded (:value link)
    nil))

(defn- inline-redex?
  "A call of a literal function with one fixed arity that does not refer to
   itself, applied to as many arguments."
  [t]
  (let [f (:fn t)]
    (and (= :fn (:op f)) (not (:recur t))
         (let [[a & more] (:arities f)]
           (and a (nil? more) (nil? (:rest a)) (= (count (:params a)) (count (:args t)))
                (not (contains? (t/free-locals (:body a)) (:self f)))
                (not (some #(= :recur (:op %)) (t/nodes (:body a)))))))))

(defn- lower*
  "Lower term `t` with prepared node `n`. `scope` is the environment layout
   (names, as in klara.runtime.prepare); `frames` are the let contexts of the
   current function around this point, innermost first, each [body-node scope]."
  [t n scope frames consts self-name self-sym osr]
  (let [selves (atom {})                 ; self name -> [fn node, free names]
        top t]
  (letfn [(constant [x]
            (let [i (count @consts)] (swap! consts conj x) (list 'clojure.core/nth 'consts i)))
          ;; a frame state's environment; a function's own name stands for the
          ;; interpreter's closure of it, so that the interpreter can recur
          (env-form [scope]
            (mapv (fn [nm]
                    (if-let [[fnode free] (get @selves nm)]
                      (list 'klara.compile.lower/interpreted (constant fnode) (vec free))
                      nm))
                  scope))
          (frames-form [frames]
            (mapv (fn [[body-node sc]] (list 'klara.compile.lower/let-frame (constant body-node) (env-form sc)))
                  frames))
          (protect
            ;; a call in a non-tail position: add this point's frames to a passing Leave
            [form frames]
            (if (empty? frames)
              form
              (list 'try form
                    (list 'catch 'clojure.lang.ExceptionInfo 'e
                          (list 'klara.compile.lower/push-frames! 'e (frames-form frames))))))
          (go [t n scope frames]
            (case (:op t)
              :const (let [x (:value t)]
                       (if (or (nil? x) (number? x) (string? x) (keyword? x) (boolean? x) (char? x))
                         x (constant x)))
              :local (:name t)
              :host (let [q (:name t)]
                      (cond (and (= "clojure.core" (namespace q)) (not (m/intrinsic? (m/host-value q)))) q
                            (:symbol (b/lookup q)) (:symbol (b/lookup q))
                            :else (constant (m/host-value q))))
              :global (let [l (:link t)]
                        (cond
                          ;; a recursive call of the definition being compiled: its own
                          ;; generation is a premise, so it denotes this function (L4.exec.valid)
                          (and (= :late (:kind l)) self-name (= (:name l) self-name)) self-sym
                          (= :late (:kind l))
                          (list 'klara.compile.lower/late (constant (Site. nil)) (list 'quote (:name l)))
                          :else (constant (link-value l))))
              :fn (let [^klara.runtime.prepare.Fn fnode n
                        self (or (:self t) (t/fresh "fn"))
                        free (:free t)
                        _ (swap! selves assoc self [fnode free])]
                    (as-> (list* 'fn* self
                           (mapv (fn [{:keys [params rest body]} ^klara.runtime.prepare.Arity a]
                                  (let [inner (cond-> (vec free)
                                                (.-self? a) (conj self)
                                                true (into params)
                                                rest (conj rest))]
                                    (list (cond-> (vec params) rest (conj '& rest))
                                          (list 'when (list 'klara.compile.lower/tick!)
                                                (list 'klara.compile.lower/leave-apply! (constant fnode) (vec free)
                                                      (if rest (list 'clojure.core/into (vec params) rest) (vec params))))
                                          (go body (.-body a) inner []))))
                                (:arities t) (.-arities fnode))) form
                      ;; L4.exec.osr: an inner function can be entered from the
                      ;; interpreter given its captured values
                      (do (when (and (not (identical? t top))
                                     ;; it must not call the outer compiled function directly
                                     (not (some #{self-sym} (filter symbol? (tree-seq coll? seq form)))))
                            (swap! osr conj [fnode (list 'fn* (vec free) form)]))
                          form)))
              :app (let [^klara.runtime.prepare.App an n
                         line (get-in t [:pos :line])
                         at (fn [form] (if (and line (seq? form)) (with-meta form {:line line}) form))
                         f (:fn t)
                         args (mapv (fn [x xn] (go x xn scope frames)) (:args t) (.-args an))]
                     (at (cond
                       (:recur t) (list* 'recur args)
                       ;; ((fn [p ..] body) a ..): the call happens in place, as a let
                       ;; with the function's entry step and frame state (L4.lower.steps)
                       (inline-redex? t)
                       (let [^klara.runtime.prepare.Fn fnode (.-f an)
                             {:keys [params body]} (first (:arities f))
                             ^klara.runtime.prepare.Arity a (first (.-arities fnode))
                             free (:free f)]
                         (protect (list 'let* (vec (interleave params args))
                                        (list 'when (list 'klara.compile.lower/tick!)
                                              (list 'klara.compile.lower/leave-apply! (constant fnode) (vec free) (vec params)))
                                        (go body (.-body a) (into (vec free) params) []))
                                  frames))
                       (and (= :host (:op f)) (= "clojure.core" (namespace (:name f)))
                            (not (m/intrinsic? (m/host-value (:name f)))))
                       (list* (:name f) args)
                       (and (= :host (:op f)) (:symbol (b/lookup (:name f))))
                       (list* (:symbol (b/lookup (:name f))) args)
                       (and self-name (= :global (:op f)) (= :late (get-in f [:link :kind])) (= self-name (get-in f [:link :name])))
                       (protect (list* self-sym args) frames)
                       :else (protect (list 'klara.compile.lower/call (go f (.-f an) scope frames) (vec args)) frames))))
              :recur (let [^klara.runtime.prepare.Recur rn n]
                       (list* 'recur (mapv (fn [x xn] (go x xn scope frames)) (:args t) (.-args rn))))
              :let (let [^klara.runtime.prepare.Let ln n
                         inner (conj scope (:name t))]
                     (list 'let* [(:name t) (go (:init t) (.-init ln) scope (cons [(.-body ln) scope] frames))]
                           (go (:body t) (.-body ln) inner frames)))
              :if (let [^klara.runtime.prepare.If in n]
                    (list 'if (go (:test t) (.-test in) scope frames)
                          (go (:then t) (.-then in) scope frames)
                          (if (:speculate t)
                            ;; L4.exec.leave: the else branch of a speculation is the reference
                            (list 'klara.compile.lower/leave-eval! (constant (.-else in)) (env-form scope) (frames-form frames))
                            (go (:else t) (.-else in) scope frames))))
              :throw (list 'throw (go (:ex t) (.-ex ^klara.runtime.prepare.Throw n) scope frames))
              (fail :L4.lower.subset (str "the backend does not compile " (:op t)))))]
    (go t n scope frames))))

(defn- compiled-nodes
  "The nodes lowering compiles: the else branch of a speculation is left to
   the interpreter (L4.exec.leave), so it need not be compilable."
  [term]
  (tree-seq (comp seq t/children)
            (fn [n] (if (and (= :if (:op n)) (:speculate n)) [(:test n) (:then n)] (t/children n)))
            term))

(defn mint-safe?
  "Does compiled code for `term` create no closures that outlive the call?
   Then it may run under a mint (L1.context.mint): its only inner functions
   are applied where they are made (loops, inlined calls)."
  [term]
  (let [applied (into #{} (comp (filter #(= :app (:op %))) (map :fn) (filter #(= :fn (:op %))) (map t/->form))
                      (compiled-nodes term))]
    (every? #(contains? applied (t/->form %))
            (filter #(= :fn (:op %)) (rest (compiled-nodes term))))))

(defn subset-violation
  "The first construct outside the compilable subset (L4.lower.subset), or nil."
  [term]
  (some (fn [n]
          (cond (contains? unsupported (:op n)) (:op n)
                (and (= :host (:op n)) (m/intrinsic? (m/host-value (:name n)))) (:name n)))
        (compiled-nodes term)))

(defn lower
  "Compile a :fn term to a host function. With :self-name, late references
   to that definition call the compiled function itself."
  ([term] (lower term {}))
  ([term {:keys [self-name]}]
   (when-not (= :fn (:op term)) (fail :L4.lower.subset "only functions are compiled"))
   (when-let [x (subset-violation term)]
     (fail :L4.lower.subset (str "the backend does not compile " x)))
   (let [consts (atom [])
         file (some #(get-in % [:pos :file]) (t/nodes term))
         self-sym (or (:self term) (t/fresh "self"))
         term (anf/anf (assoc term :self self-sym))
         node (m/prepare-term term)
         osr (atom [])
         form (lower* term node [] () consts self-name self-sym osr)
         osr-entries @osr
         wrapper (list 'fn* ['consts] (vector form (mapv second osr-entries)))
         [f factories] ((with-bindings {#'*ns* (the-ns 'klara.compile.lower)
                                        clojure.lang.Compiler/SOURCE_PATH (or file "klara")
                                        clojure.lang.Compiler/SOURCE (if file (.getName (java.io.File. ^String file)) "klara")}
                          (eval wrapper))
                        @consts)]
     {:form form
      :anf term
      ;; compiled code reports the Klara source file and lines (L0.trace.positions)
      :fn f
      ;; [fn-node factory]: factory of captured values -> compiled function
      :osr (mapv (fn [[fnode _] factory] [fnode factory]) osr-entries factories)})))
