(ns klara.formal.certify
  "The ansatz certifier for proof-carrying candidates (L4.check.certificate).

  Reflection: the reference and candidate Core terms are quoted into the
  formal Tm by the same bridge the differential tests trust, rendered as
  kernel terms, and the certifier states the theorem about exactly those
  terms. For a unary function on 64-bit integers:

    forall i : Int, inRange i ->
      forall terminal d, Star (ref i) d <-> Star (cand i) d

  The certificate supplies the proof: tactic forms in which `%ref` and
  `%cand` stand for the two configurations, `%ref-body`/`%cand-body` for the
  function bodies, `%arg` for the argument, `%world`/`%worlds` for the empty
  world and world table. The kernel checks it; nothing
  else about the certificate is trusted. The assumption `inRange i` becomes
  the runtime guard `:long` on the argument."
  (:require [ansatz.core :as a]
            [clojure.walk :as walk]
            [klara.compile.kernel :as kernel]
            [klara.formal.bridge :as bridge]
            [klara.formal.checker]))

;; ---------------------------------------------------------------------------
;; Runtime Tm values as kernel terms

(defn- int-term [n]
  (if (neg? n) (list 'Int.negSucc (- (- n) 1)) (list 'Int.ofNat n)))

(defn- datum-term [[tag x]]
  (case (int tag)
    0 'Datum.nil
    1 (list 'Datum.bool (if x 'Bool.true 'Bool.false))
    2 (list 'Datum.int (int-term x))
    3 (list 'Datum.kw x)))

(def ^:private prim-name {nil 'PrimOp.add 1 'PrimOp.sub 2 'PrimOp.mul 3 'PrimOp.eq 4 'PrimOp.lt})

(defn tm-term
  "A runtime Tm (bridge representation) as an ansatz surface term."
  [x]
  (let [[tg & fs] x
        nm (bridge/tag-name (int tg))
        sub (fn [v] (tm-term v))]
    (case nm
      :var (list 'Tm.var (first fs))
      :lit (list 'Tm.lit (datum-term (first fs)))
      :lam (list 'Tm.lam (sub (first fs)))
      :app (list 'Tm.app (sub (nth fs 0)) (sub (nth fs 1)))
      :let (list 'Tm.let_ (sub (nth fs 0)) (sub (nth fs 1)))
      :if (list 'Tm.if_ (sub (nth fs 0)) (sub (nth fs 1)) (sub (nth fs 2)))
      :fix (list 'Tm.fix (sub (first fs)))
      :glob (list 'Tm.glob (first fs))
      :prim (list 'Tm.prim (prim-name (first fs)) (sub (nth fs 1)) (sub (nth fs 2)))
      (throw (ex-info (str "the certifier does not support " nm " yet") {::unsupported nm})))))

;; ---------------------------------------------------------------------------
;; The theorem and its check

(defn- config [t] (list 'Config.mk 'World.empty 'Worlds.none 0 t))

(defn statement
  "The equivalence of unary integer functions `ref` and `cand` (kernel terms)."
  [ref cand]
  (let [arg '(Tm.lit (Datum.int i))
        cr (config (list 'Tm.app ref arg))
        cc (config (list 'Tm.app cand arg))]
    {:ref-config cr :cand-config cc
     :params '[i :- Int, hi :- (= Bool (inRange i) Bool.true)]
     :type (list 'forall '[d :- Config]
                 (list '=> '(forall [e :- Config] (Not (Step d e)))
                       (list 'And (list '=> (list 'Star cr 'd) (list 'Star cc 'd))
                             (list '=> (list 'Star cc 'd) (list 'Star cr 'd)))))}))


(defn certify
  "Check `certificate` for `reference` = `candidate` (Core :fn terms)."
  [{:keys [reference candidate certificate]}]
  (try
    (let [ctx (bridge/new-ctx)
          ref (tm-term (bridge/quote-term ctx reference))
          cand (tm-term (bridge/quote-term ctx candidate))
          {:keys [ref-config cand-config params type]} (statement ref cand)
          body (fn [t] (if (= 'Tm.lam (first t)) (second t) t))
          tactics (walk/postwalk-replace {'%ref ref-config '%cand cand-config
                                          '%ref-term ref '%cand-term cand
                                          '%ref-body (body ref) '%cand-body (body cand)
                                          '%arg '(Tm.lit (Datum.int i))
                                          '%world 'World.empty '%worlds 'Worlds.none}
                                         (:proof certificate))
          ;; unique per check: the kernel environment rejects redeclaration
          name (symbol (str "Klara.certificate." (.replace (str (java.util.UUID/randomUUID)) "-" "")))]
      (binding [*ns* (the-ns 'klara.formal.checker)]
        (eval (list* 'ansatz.core/theorem name params type tactics)))
      {:result :proved :guards [:long]
       :evidence {:kernel :ansatz :theorem name :statement type}})
    (catch Throwable e
      {:result :failed
       :message (loop [e e] (if (.getCause e) (recur (.getCause e)) (.getMessage e)))})))

(kernel/register-certifier! :ansatz certify)

;; ---------------------------------------------------------------------------
;; klara.proof/certify: the certifier as a guest function, so proof search can
;; be ordinary Klara code (for example in a budgeted job). It returns data: a
;; result map whose :evidence names the kernel-checked theorem.

(klara.lang.builtins/register!
 'klara.proof/certify
 {:kind :host
  :fn (fn [reference candidate proof]
        (certify {:reference (.-term ^klara.runtime.value.Code reference)
                  :candidate (.-term ^klara.runtime.value.Code candidate)
                  :certificate {:kind :ansatz :proof proof}}))})
