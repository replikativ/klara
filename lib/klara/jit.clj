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

(defn speculate-branches
  "Speculate that branches the profile never saw taken stay cold. The hot
   path compiles; reaching a cold branch leaves to the interpreter at that
   point (L4.exec.leave), which may then do anything the reference does:
   perform effects, call host code, run uncompilable constructs."
  [c]
  (let [rebuilt (code/with-children c (mapv speculate-branches (code/children c)))
        v (code/view c)
        p (when (= :if (:op v)) (:profile v))]
    (if p
      (let [[_ then' else'] (code/children rebuilt)]
        (cond (and (zero? (:else p)) (>= (:then p) hot) (admissible? (:test v) c))
              (guard (:test v) then' c)
              (and (zero? (:then p)) (>= (:else p) hot) (admissible? (negate (:test v)) c))
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

(defn default
  "The default specializer: speculate on cold branches, inline hot calls of
   small definitions. Specialization on stable values comes next
   (design/06-speculation.md#4)."
  [ctx]
  (-> (:reference ctx) speculate-branches inline-calls))

(defn specialize
  "Run the definition's specializer, or the default."
  [ctx]
  (if-let [s (:specializer ctx)]
    (s ctx default)
    (default ctx)))

(defn compile!
  "Specialize, check, compile and install the definition named q. Returns the
   preparation outcome. opts may name a :specializer to use instead of the
   attached one; other options go to compiler/prepare."
  ([q] (compile! q {}))
  ([q opts]
   (let [ctx (cond-> (context q) (:specializer opts) (assoc :specializer (:specializer opts)))
         candidate (specialize ctx)
         outcome (compiler/prepare (:reference ctx)
                                   (merge {:recipe (fn [_] candidate) :name q} (dissoc opts :specializer)))]
     (when (= :ready (:status outcome))
       (compiler/install! outcome))
     outcome)))
