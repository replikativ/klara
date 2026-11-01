(ns klara.jit
  "The programmable JIT (design/06-speculation.md#6-specializers).

  A specializer is a pure function (fn [ctx default] code) called with a
  context built from the definition, its profile and the host, and the
  default specializer. It returns candidate Code for the definition, which
  the kernel checks like any candidate. Attach one with

    (defn ^{:klara/specialize my-specializer} f [..] ..)

  and compile with (jit/compile! 'ns/f). guard, same?, context and function
  are runtime functions of this namespace; the rest is Klara code."
  (:require [klara.code :as code]
            [klara.compiler :as compiler]))

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

(defn- cold? [taken other]
  (and (>= other hot) (<= (* taken rare) other)))

(defn speculate-branches
  "Speculate that branches the profile (almost) never saw taken stay cold. The hot
   path compiles; reaching a cold branch leaves to the interpreter at that
   point (L4.exec.leave), which may then do anything the reference does:
   perform effects, call host code, run uncompilable constructs."
  [c]
  (let [rebuilt (code/with-children c (mapv speculate-branches (code/children c)))
        v (code/view c)
        p (when (= :if (:op v)) (:profile v))]
    (if p
      (let [[_ then' else'] (code/children rebuilt)]
        (cond (and (cold? (:else p) (:then p)) (admissible? (:test v) c))
              (guard (:test v) then' c)
              (and (cold? (:then p) (:else p)) (admissible? (negate (:test v)) c))
              (guard (negate (:test v)) else' c)
              :else rebuilt))
      rebuilt)))

(defn size [c] (inc (reduce + 0 (map size (code/children c)))))

(def small
  "Nodes in a function small enough to inline."
  40)

(defn inline-calls
  "Inline hot calls of small function definitions: (f x) becomes
   ((fn [p] body) x). The checker accepts it by unfolding f, which makes f's
   generation a premise: redefining f retires the compiled code."
  [c]
  (let [rebuilt (code/with-children c (mapv inline-calls (code/children c)))
        v (code/view c)]
    (if (= :app (:op v))
      (let [f (code/view (:fn v))
            callee (when (and (= :global (:op f)) (= :late (:kind f))
                              (>= (or (:count (:profile v)) 0) hot))
                     (callee-code (:name f)))]
        (if (and callee (<= (size callee) small))
          (code/make {:op :app :fn callee :args (rest (code/children rebuilt))})
          rebuilt))
      rebuilt)))

(def large
  "Nodes a call specialized to its known arguments may grow to."
  400)

(defn- calls? [c q]
  (let [v (code/view c)]
    (or (and (= :global (:op v)) (= q (:name v)))
        (boolean (some #(calls? % q) (code/children c))))))

(defn specialize-known-calls
  "Specialize hot calls whose arguments include constants or data
   definitions, by partial evaluation (simplify). The caller then needs none
   of the callee's guards on those arguments: the checker accepts the
   residual by unfolding the callee and the data, whose generations become
   premises (L4.check.delta-data). Kept only when the call is gone and the
   residual is not large."
  [c]
  (let [rebuilt (code/with-children c (mapv specialize-known-calls (code/children c)))
        v (code/view c)
        f (when (= :app (:op v)) (code/view (:fn v)))]
    (if (and f (= :global (:op f)) (>= (or (:count (:profile v)) 0) hot)
             (some known? (:args v)))
      (let [s (simplify rebuilt)]
        (if (and (not (calls? s (:name f))) (<= (size s) large)) s rebuilt))
      rebuilt)))

(defn default
  "The default specializer: speculate on cold branches, specialize calls to
   their known arguments, inline hot calls of small definitions
   (design/06-speculation.md#4)."
  [ctx]
  (-> (:reference ctx) speculate-branches specialize-known-calls inline-calls))

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
   (let [ctx (cond-> (context q (:profile opts)) (:specializer opts) (assoc :specializer (:specializer opts)))
         candidate (specialize ctx)
         outcome (compiler/prepare (:reference ctx)
                                   (merge {:recipe (fn [_] candidate) :name q}
                                          (dissoc opts :specializer :profile :specializer-name)))]
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
