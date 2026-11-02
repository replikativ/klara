(ns klara.jit
  "The programmable JIT (design/06-speculation.md#6-specializers-the-jit-is-programmable).

  A specializer is a pure function (fn [ctx default] code) called with a
  context built from the definition, its profile and the host, and the
  default specializer. It returns candidate Code for the definition, which
  the kernel checks like any candidate. Attach one with

    (defn ^{:klara/specialize my-specializer} f [..] ..)

  and compile with (jit/compile! 'ns/f); a specializer may decline (nil).

  Runtime functions of this namespace (the rest is Klara code):
    context      the context of a definition (L4.jit.context)
    guard        a speculation (if guard specialized reference) (L4.check.speculate)
    same?        the value-speculation guard (L4.check.speculate-value)
    admissible?  whether a guard is admissible for a reference (L4.check.speculate)
    pure?        the purity fact of a definition (L4.facts.pure)
    effect       its effect class (L4.facts.effect)"
  (:require [klara.code :as code]
            [klara.compiler :as compiler]
            [klara.jit.staged :as staged]
            [klara.jit.rules :as jit-rules]))

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

(defn events
  "Everything the definition's profile counted (calls, entries, branches
   taken), summed: proportional to the interpreter's work in its body (its
   callees count in their own profiles)."
  [ctx]
  (reduce + 0 (counts (:reference ctx))))

(defn params [ctx] (:params (code/view (:reference ctx))))

(defn body [ctx] (:body (code/view (:reference ctx))))

(defn reference-body
  "The definition's body over the given parameter code (inside jit/function)."
  [ctx & args]
  (code/subst (body ctx) (zipmap (params ctx) args)))

(defn function
  "The candidate function for the definition: fresh parameters for its
   arity, passed to `f` as code; `f` returns the body (L4.jit.function,
   built with code/fn*, L2.code.binders)."
  [ctx f]
  (code/fn* (count (params ctx)) (fn [self & ps] (apply f ps))))

;; ---------------------------------------------------------------------------
;; Specializing and compiling

(def rules
  "Rules the default specializer consults (design/09-extensions.md,
   L4.jit.rules): a definition, so libraries extend it and redefining it
   retires what it produced."
  [])

(defn default
  "The default specializer: the staged interpreter (klara.jit.staged,
   design/08-staged-jit.md) on the definition's reference and profile. It
   unfolds known functions on known arguments, inlines hot calls of small
   definitions and speculates on cold branches, stable arguments and single
   callees. A callee that loops is not inlined where the backend makes an
   inlined loop (no longer in return position) cost more."
  ([ctx] (default ctx {}))
  ([ctx pol]
   (let [p (merge {:inline-loops? (not= :closure (get-in ctx [:runtime :backend :loop-outside-return]))
                   ;; the world's rules, then the preparation's (L4.jit.rules)
                   :rules (into rules (get-in ctx [:policy :rules]))}
                  (dissoc (:policy ctx) :rules)
                  pol)]
     ;; then the default's own (klara.jit.rules), unless the policy says :builtin-rules false
     (staged/specialize ctx (update p :rules (fn [rs] (into (vec rs) (when-not (false? (:builtin-rules p)) jit-rules/builtin))))))))

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
                                   ;; fired rules are collected inside the job (an atom made
                                   ;; outside may not be changed there) and carried out
                                   (merge {:recipe (fn [_] (let [fired (atom [])
                                                                 c (specialize (assoc ctx :fired fired))]
                                                             {:code c :provenance {:rules (vec (distinct @fired))}}))
                                           :name q}
                                          (dissoc opts :specializer :profile :specializer-name :policy)))]
     ;; L4.exec.provenance: how this candidate came about
     (assoc outcome :provenance
            {:specializer (or (:specializer-name opts)
                              (when (:specializer ctx) (:specializer-name ctx))
                              :default)
             :profile {:work (work ctx) :calls (calls ctx) :saved (some? (:profile opts))}
             ;; the rules that fired in generating it (L4.jit.rules)
             :rules (get-in outcome [:recipe-provenance :rules] [])}))))

(defn compile!
  "Prepare the definition named q (see prepare) and install it when ready.
   Returns the preparation outcome."
  ([q] (compile! q {}))
  ([q opts]
   (let [outcome (prepare q opts)]
     (when (= :ready (:status outcome))
       (compiler/install! outcome))
     outcome)))
