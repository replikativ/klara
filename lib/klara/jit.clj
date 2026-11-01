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

(defn default
  "The default specializer: the definition as it is. (The staged default of
   design/06-speculation.md#4 replaces it.)"
  [ctx]
  (:reference ctx))

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
