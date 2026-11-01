(ns klara.compiler
  "Checked compilation (spec/L4-compiler.md, design/02-compilation.md).

  This namespace is ordinary Klara code over the trusted kernel
  (klara.compiler.kernel). Recipes and policies are untrusted guest
  functions; only the kernel's checker decides what is admitted."
  (:require [klara.compiler.kernel :as kernel]
            [klara.jit.staged :as staged]))

(defn as-is
  "The recipe that proposes the reference itself: plain compilation."
  [reference]
  reference)

(defn prepare
  "Run `(:recipe opts)` on `reference` in a job under `(:budget opts)`, check
   the result against `reference` and compile it. Returns an outcome map
   with :status :ready, :rejected or :exhausted."
  ([reference] (prepare reference {}))
  ([reference opts] (kernel/prepare reference opts)))

(defn executable
  "A function that runs the prepared candidate where its premises hold,
   and the reference meaning elsewhere."
  [outcome]
  (kernel/executable outcome))

(defn reference
  "Code for the current definition of the function named `q`."
  [q]
  (kernel/reference q))

(defn install!
  "Make calls to the definition use the candidate wherever it is valid."
  [outcome]
  (kernel/install! outcome))

(defn pin
  "`c` with every late link pinned to world `w` (AOT, L4.pin.links)."
  [c w]
  (kernel/pin c w))

(defn explain
  "Data describing how a function is executed."
  [f]
  (kernel/explain f))

(defn optimize!
  "Prepare the definition named `q` with a recipe (default: as-is) and
   install it when ready. Returns the outcome."
  ([q] (optimize! q {}))
  ([q opts]
   (let [outcome (prepare (reference q) (assoc opts :name q))]
     (when (= :ready (:status outcome))
       (install! outcome))
     outcome)))

(defn specialize
  "A compiled version of `f` with the arguments in `known` (index -> value)
   fixed, checked against `(fn [..] (f ..))`. The default recipe is the
   staged interpreter's residual (klara.jit.staged/residual): it unfolds f
   on the known arguments and computes what they decide. Returns the executable, or
   the outcome when preparation did not succeed."
  ([f known] (specialize f known {}))
  ([f known opts]
   (let [outcome (prepare (kernel/specialization f known)
                          (merge {:recipe staged/residual} opts))]
     (if (= :ready (:status outcome))
       (executable outcome)
       outcome))))
