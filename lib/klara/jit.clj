(ns klara.jit
  "The programmable JIT (design/06-speculation.md#6-specializers).

  A specializer is a pure function (fn [ctx default] code) called with a
  context built from the definition, its profile and the host, and the
  default specializer. It returns candidate Code for the definition, which
  the kernel checks like any candidate. Attach one with

    (defn ^{:klara/specialize my-specializer} f [..] ..)

  and compile with (jit/compile! 'ns/f); a specializer may decline (nil).

  Runtime functions of this namespace (the rest is Klara code):
    context      the context of a definition (L4.jit.context)
    function     a candidate function with fresh parameters (L4.jit.function)
    guard        a speculation (if guard specialized reference) (L4.check.speculate)
    same?        the value-speculation guard (L4.check.speculate-value)
    admissible?  whether a guard is admissible for a reference (L4.check.speculate)
    pure?        the purity fact of a definition (L4.facts.pure)"
  (:require [klara.code :as code]
            [klara.compiler :as compiler]
            [klara.compiler.recipes :as recipes]))

;; ---------------------------------------------------------------------------
;; Reading the context

(defn stable?
  "Did argument i always have the same value?"
  [ctx i]
  (let [s (get-in ctx [:profile :entries :stable i])]
    (and (vector? s) (= :value (first s)))))

(defn stable-value [ctx i] (second (get-in ctx [:profile :entries :stable i])))

(defn arg-class
  "The class argument i always had, or nil if it varied."
  [ctx i]
  (let [c (get-in ctx [:profile :entries :classes i])]
    (when-not (= :polymorphic c) c)))

(defn calls [ctx] (get-in ctx [:profile :entries :count]))

(defn- counts [c]
  (let [p (:profile (code/view c))]
    (cons (or (:count p) (when p (+ (:then p 0) (:else p 0))) 0)
          (mapcat counts (code/children c)))))

(defn work
  "How much the definition ran: the largest count in its profile, so a
   loop's iterations count, not only the calls of the function."
  [ctx]
  (apply max 0 (counts (:reference ctx))))

(defn params [ctx] (:params (code/view (:reference ctx))))

(defn body [ctx] (:body (code/view (:reference ctx))))

(defn reference-body
  "The definition's body over the given parameter code (inside jit/function)."
  [ctx & args]
  (code/subst (body ctx) (zipmap (params ctx) args)))

;; (jit/function ctx (fn [x y] body)) builds the candidate function: fresh
;; parameters, passed to the body function as code. It is a runtime function
;; of this namespace.

;; ---------------------------------------------------------------------------
;; Specializing and compiling

(defn negate [test]
  (code/make {:op :app :fn (code/make {:op :host :name 'clojure.core/not}) :args [test]}))

(def hot
  "Observations of an if before its profile counts as evidence."
  100)

(def rare
  "A branch taken at most once in this many observations counts as cold."
  10000)

(def small
  "Nodes in a function small enough to inline."
  40)

(def large
  "Nodes a call specialized to its known arguments may grow to."
  400)

(defn- policy
  "Thresholds of the default specializer; (:policy opts) of prepare overrides them."
  [p]
  (merge {:hot hot :rare rare :small small :large large} p))

(defn- cold? [p taken other]
  (and (>= other (:hot p)) (<= (* taken (:rare p)) other)))

(defn speculate-branches
  "Speculate that branches the profile (almost) never saw taken stay cold. The hot
   path compiles; reaching a cold branch leaves to the interpreter at that
   point (L4.exec.leave), which may then do anything the reference does:
   perform effects, call host code, run uncompilable constructs."
  ([c] (speculate-branches c {}))
  ([c pol]
  (let [pol (policy pol)
        rebuilt (code/with-children c (mapv #(speculate-branches % pol) (code/children c)))
        v (code/view c)
        p (when (= :if (:op v)) (:profile v))]
    (if p
      (let [[_ then' else'] (code/children rebuilt)]
        (cond (and (cold? pol (:else p) (:then p)) (admissible? (:test v) c))
              (guard (:test v) then' c)
              (and (cold? pol (:then p) (:else p)) (admissible? (negate (:test v)) c))
              (guard (negate (:test v)) else' c)
              :else rebuilt))
      rebuilt))))

(defn size [c] (inc (reduce + 0 (map size (code/children c)))))

(defn- loops?
  "Does c contain a loop (a recur)?"
  [c]
  (or (= :recur (:op (code/view c)))
      (boolean (some loops? (code/children c)))))

(defn inline-calls
  "Inline hot calls of small function definitions other than `self` (whose
   own calls are direct): (f x) becomes ((fn [p] body) x). The checker
   accepts it by unfolding f, which makes f's generation a premise:
   redefining f retires the compiled code."
  ([c self] (inline-calls c self {}))
  ([c self pol]
  (let [pol (policy pol)
        rebuilt (code/with-children c (mapv #(inline-calls % self pol) (code/children c)))
        v (code/view c)]
    (if (= :app (:op v))
      (let [f (code/view (:fn v))
            callee (when (and (= :global (:op f)) (= :late (:kind f)) (not= self (:name f))
                              (>= (or (:count (:profile v)) 0) (:hot pol)))
                     (code/unfold (:fn v)))]
        ;; a callee with a loop stays a call where the backend says an inlined
        ;; loop (no longer in return position) costs more (:inline-loops? of
        ;; the policy, from the context's :runtime :backend)
        (if (and callee (<= (size callee) (:small pol)) (or (:inline-loops? pol) (not (loops? callee))))
          (code/make {:op :app :fn callee :args (rest (code/children rebuilt))})
          rebuilt))
      rebuilt))))

(defn- calls? [c q]
  (let [v (code/view c)]
    (or (and (= :global (:op v)) (= q (:name v)))
        (boolean (some #(calls? % q) (code/children c))))))

(defn specialize-known-calls
  "Specialize hot calls whose arguments include constants or data
   definitions, by partial evaluation (klara.compiler.recipes/inline). The caller then needs none
   of the callee's guards on those arguments: the checker accepts the
   residual by unfolding the callee and the data, whose generations become
   premises (L4.check.delta-data). Kept only when the call is gone and the
   residual is not large."
  ([c] (specialize-known-calls c {}))
  ([c pol]
  (let [pol (policy pol)
        rebuilt (code/with-children c (mapv #(specialize-known-calls % pol) (code/children c)))
        v (code/view c)
        f (when (= :app (:op v)) (code/view (:fn v)))]
    (if (and f (= :global (:op f)) (>= (or (:count (:profile v)) 0) (:hot pol))
             (some #(some? (code/known %)) (:args v)))
      (let [s (recipes/inline rebuilt)]
        (if (and (not (calls? s (:name f))) (<= (size s) (:large pol))) s rebuilt))
      rebuilt))))

(defn default
  "The default specializer: speculate on cold branches, specialize calls to
   their known arguments, inline hot calls of small definitions
   (design/06-speculation.md#4)."
  [ctx]
  (let [p (merge {:inline-loops? (not= :closure (get-in ctx [:runtime :backend :loop-outside-return]))}
                 (:policy ctx))]
    (-> (:reference ctx)
        (speculate-branches p)
        (specialize-known-calls p)
        (inline-calls (:name ctx) p))))

(defn specialize
  "Run the definition's specializer, or the default."
  [ctx]
  (if-let [s (:specializer ctx)]
    (s ctx default)
    (default ctx)))

(defn prepare
  "Specialize and check the definition named q, without installing it.
   opts may name a :specializer to use instead of the attached one and a
   saved :profile; other options go to compiler/prepare."
  ([q] (prepare q {}))
  ([q opts]
   (let [ctx (cond-> (assoc (context q (:profile opts)) :policy (:policy opts))
               (:specializer opts) (assoc :specializer (:specializer opts)))
         ;; the specializer runs as the recipe, inside the preparation job:
         ;; budgeted, isolated, its work counted (L4.prepare.job)
         outcome (compiler/prepare (:reference ctx)
                                   (merge {:recipe (fn [_] (specialize ctx)) :name q}
                                          (dissoc opts :specializer :profile :specializer-name :policy)))]
     ;; L4.exec.provenance: how this candidate came about
     (assoc outcome :provenance
            {:specializer (or (:specializer-name opts)
                              (when (:specializer ctx) (:specializer-name ctx))
                              :default)
             :profile {:work (work ctx) :calls (calls ctx) :saved (some? (:profile opts))}}))))

(defn compile!
  "Prepare the definition named q (see prepare) and install it when ready.
   Returns the preparation outcome."
  ([q] (compile! q {}))
  ([q opts]
   (let [outcome (prepare q opts)]
     (when (= :ready (:status outcome))
       (compiler/install! outcome))
     outcome)))
