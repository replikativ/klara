;; # Klara's compiler, pass by pass
;;
;; This notebook runs real definitions through Klara's compile tier and shows
;; every intermediate term. Everything is computed live from the current code,
;; so it stays in sync with the implementation. Render it with Clay
;; (`clojure -M:notebook`, then `(scicloj.clay.v2.api/make! {:source-path
;; "notebooks/compiler_walkthrough.clj"})`) or evaluate it form by form at a REPL.
;;
;; The pipeline:
;;
;; ```
;; source ─reader─▶ forms ─expand─▶ K0 core term   (stored in the world as a closure with a CodeId;
;;                                     │             T0 interprets it immediately)
;;                    :repl/compile ───┘
;;   speculate ─▶ inline ─▶ lower ─▶ PE ─▶ escape ─▶ PE ─▶ emit ─▶ install in the stage cache
;; ```
;;
;; T0, the reference interpreter, defines meaning. Every pass has an obligation
;; (stated in its namespace docstring) and compiled code is a cache entry:
;; deleting it changes no observation.

(ns compiler-walkthrough
  (:require [clojure.pprint :as pp]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [scicloj.kindly.v4.kind :as kind]
            [klara.code :as code]
            [klara.compile.core :as cc]
            [klara.compile.emit :as emit]
            [klara.compile.escape :as escape]
            [klara.compile.inline :as inline]
            [klara.compile.ir :as ir]
            [klara.compile.pe :as pe]
            [klara.compile.speculate :as speculate]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.repl :as repl]
            [klara.world :as w]))

;; ## Helpers
;;
;; Named IR terms are printed as Klara-like source. Generated names (`v3419`,
;; `args3420`, …) are renamed to stable short names per printed form, so the
;; output reads the same on every run.

(defn- stable-names [form]
  (let [seen (atom {})
        pat #"^(v|args|field|livefield|extent|operation|abort|handler)(\d+)$"]
    (walk/postwalk
     (fn [x]
       (if-let [[_ base] (and (symbol? x) (re-matches pat (name x)))]
         (or (@seen x)
             (let [n (symbol (str base (inc (count (filter #(str/starts-with? (name %) base)
                                                            (vals @seen))))))]
               (swap! seen assoc x n) n))
         (if (symbol? x) (symbol (name x)) x)))
     form)))

(defn- named->form [t]
  (letfn [(go [t]
            (case (:op t)
              :local (:name t)
              :quote (let [d (:datum t)] (if (or (symbol? d) (seq? d)) (list 'quote d) d))
              :resolve (:id t)
              :prim (list* (:name t) (map go (:args t)))
              :fn (list 'fn (vec (:params t)) (go (:body t)))
              :app (list* (go (:fn t)) (map go (:args t)))
              :let (list 'let [(:name t) (go (:init t))] (go (:body t)))
              :if (list 'if (go (:test t)) (go (:then t)) (go (:else t)))
              :letrec (list 'letrec (vec (mapcat (fn [n i] [n (go i)]) (:names t) (:inits t)))
                            (go (:body t)))
              :perform (list* 'perform (some-> (:target t) go) (:name t) (map go (:args t)))
              :handle (list 'handle (:name t)
                            (into {} (map (fn [[k v]] [k (go v)]) (:clauses t))) (go (:body t)))
              (list (:op t) '…)))]
    (go t)))

(defn- show [form]
  (kind/code (with-out-str (binding [pp/*print-right-margin* 90]
                             (pp/pprint (stable-names form))))))

(def session (repl/session))
(defn- k! [src] (repl/eval-string session src))
(defn- world [] (:world (get @(:worlds session) @(:current session))))

(defn passes
  "Run every pass on a world definition and return the intermediate terms."
  [sym]
  (let [basis (w/snapshot (world))
        source (ev/closure-term (:value (w/entry* basis sym)))
        sp (speculate/run (ir/named source) (c/code-id source))
        i (inline/run (:term sp) basis 4)
        k1 (ir/lower (:term i))
        p (pe/run k1 10)
        a (escape/run (:term p))
        q (pe/run (:term a) 10)]
    {:k0 (code/core->form source)
     :inline (named->form (:term i)) :guards (:guards i)
     :classes (frequencies (keep :class (ir/nodes k1)))
     :pe (named->form (:term p))
     :escape (named->form (:term q)) :removed (:allocations-removed a)
     :emitted (:form (emit/run (:term q)))
     :installed (:form (cc/compile-def (world) sym {}))}))

;; ## 1. The baseline path: `sq-plus`

(k! "(defn sq-plus [n] (+ (* n n) 3))")

(def sq (passes 'sq-plus))

;; The expander produced this core term, stored in the world with a CodeId:
(show (:k0 sq))

;; Nothing to inline, fold or replace. The emitted Clojure uses
;; `clojure.core`'s arithmetic, so overflow and ratios behave exactly as in T0:
(show (:installed sq))

(k! ":repl/compile sq-plus")
[(k! "(sq-plus 3)") (k! "(sq-plus 1/2)") (k! "(sq-plus 3037000500)")]

;; ## 2. Inlining, guards and redefinition: `twice-inc`

(k! "(defn inc2 [x] (+ x 2))")
(k! "(defn twice-inc [n] (* (inc2 n) 2))")

(def ti (passes 'twice-inc))

;; Inline substitutes `inc2`'s closure and records a guard on its value-id:
(show (:inline ti))
(:guards ti)

;; Partial evaluation beta-reduces the inlined call:
(show (:pe ti))

;; The lifecycle at the REPL. Redefining `inc2` publishes a new world root; no
;; cache is touched (gate R1). At the next call the executable's verdict for
;; the new root fails, the call runs in T0 with the new `inc2`, and a
;; recompile produces a new executable.
(mapv (juxt identity k!)
      [":repl/compile twice-inc" "(twice-inc 5)"
       "(defn inc2 [x] (+ x 100))" "(twice-inc 5)"
       ":repl/compile twice-inc" "(twice-inc 5)"])

;; ## 3. Escape analysis and scalar replacement: `pair-sum`

(k! "(defn pair-sum [n] (let [v [n (+ n 1)]] (+ (first v) (second v))))")

(def ps (passes 'pair-sum))

;; Before escape analysis, the vector is built:
(show (:pe ps))

;; `v` is used only by projections on a vector literal, so it does not escape
;; and is never allocated. Field evaluation order is preserved:
(show (:escape ps))
(:removed ps)

;; ## 4. Closure elimination: `adder`

(k! "(defn adder [n] (let [k (fn [a] (+ a n))] (+ (k 2) (k 3))))")

(def ad (passes 'adder))
(show (:pe ad))

;; `k` is only called directly, so each call site gets a freshly renamed copy,
;; which partial evaluation then beta-reduces:
(show (:escape ad))

;; ## 5. Loops become JVM loops: `sum-to`

(k! "(defn sum-to [n] (loop [i n acc 0] (if (> i 0) (recur (dec i) (+ acc i)) acc)))")

(def st (passes 'sum-to))

;; The expander turned `loop`/`recur` into a `letrec` with a self tail call:
(show (:k0 st))

;; The emitter turns a single self-recursive `letrec` into a JVM loop, with
;; primitive locals where a guard licenses them (S11):
(show (:installed st))

;; ## 6. Effect handlers compiled away: `weighted`

(k! (str "(defn weighted [n] (handle [h {:weight (fn [x k] (k (* x 2)))}]"
           " (+ (perform h :weight n) (perform h :weight (+ n 1)))))"))

(def wt (passes 'weighted))

;; Both performs are tail-resumptive (the clause calls `k` once, in tail
;; position), so no continuation is needed:
(:classes wt)

;; The clause becomes a plain function and each perform a direct call; the
;; `try` serves abortive clauses, which unwind with an extent token:
(show (:installed wt))

;; ## 7. Speculation with a mid-body guard and deopt: `spec`

(k! "(defn spec [x y] (let [k (fn [a] (* a 2)) v [x y]] (+ x (k y))))")

(def sp (passes 'spec))

;; The speculative code has three paths: the generic one after repeated
;; deopts, the guarded fast path, and `deopt!` with a frame state from which
;; T0 resumes exactly at the guard (rebuilding the elided closure and vector):
(show (:installed sp))

(k! ":repl/compile spec")
[(k! "(spec 1 2)") (k! "(spec 1 2.5)") (k! "(spec 1.5 2)")]

;; ## What gets installed
;;
;; Every compiled definition is a cache entry with its guards, a certificate
;; (`:tested` here; S3's fusion carries ansatz theorems instead) and a pass log:

(-> (cc/compile-def (world) 'twice-inc {})
    (select-keys [:name :code-id :guards :certificate :pass-log]))
