(ns klara.fusion.kernel
  "The ansatz side of S3: kernel-term helpers, the two fusion laws (stated
  and proved here, checked by the ansatz kernel), the proof environment
  Klara certifies against, and the fingerprints a certificate records
  (checker version, store cohort, dependency closure).

  The laws (universe 0, polymorphic in the element types):

    Klara.foldl_map    : ∀ α β γ (f : γ → β → γ) (g : α → β) (l : List α) (b : γ),
                         foldl f b (map g l) = foldl (λ acc x. f acc (g x)) b l
    Klara.foldl_filter : ∀ α γ (f : γ → α → γ) (p : α → Bool) (l : List α) (b : γ),
                         foldl f b (filter p l)
                           = foldl (λ acc x. cond (p x) (f acc x) acc) b l

  Both are proved by List.rec with the accumulator generalized; the
  filter case splits on (p hd) with Bool.rec, using a motive in which
  `filter p (hd :: tl)` is written as `cond c (hd :: filter p tl)
  (filter p tl)`, which is definitionally equal at c := p hd. No Init
  lemma is cited, so the laws check against the bundled medium Init tier
  (3653 declarations) and need no external store.

  The proof environment is an immutable ansatz Env value captured once:
  later changes to ansatz's global session (e.g. wandler loading the full
  Init) do not affect what Klara's certificates are checked against."
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [clojure.java.io :as io]
            [klara.core :as kc])
  (:import [ansatz.kernel Env TypeChecker]))

;; ---------------------------------------------------------------------------
;; term helpers
;; ---------------------------------------------------------------------------

(def l0 lvl/zero)
(def l1 (lvl/succ lvl/zero))

(defn c
  "Constant n at universe levels ls (Level values)."
  ([n] (c n []))
  ([n ls] (e/const' (nm/from-string n) (vec ls))))

(def Nat (c "Nat"))
(def Bool (c "Bool"))
(def Type0 (e/sort' l1))
(defn List [a] (e/app (c "List" [l0]) a))
(defn arrow [a b] (e/forall' "_" a b :default))

(def ^:private fresh (atom 7300000))
(defn fvar! "A fresh free variable id." [] (swap! fresh inc))

(defn lam*
  "λ over [[fvar-id name type] ..] (outermost first), abstracting the fvars."
  [binders body]
  (reduce (fn [b [id n ty]] (e/lam n ty (e/abstract1 b id) :default))
          body (reverse binders)))

(defn pi*
  "∀ over [[fvar-id name type] ..] (outermost first)."
  [binders body]
  (reduce (fn [b [id n ty]] (e/forall' n ty (e/abstract1 b id) :default))
          body (reverse binders)))

(defn foldl [acc-ty el-ty f init l] (e/app* (c "List.foldl" [l0 l0]) acc-ty el-ty f init l))
(defn lmap [a b f l] (e/app* (c "List.map" [l0 l0]) a b f l))
(defn lfilter [a p l] (e/app* (c "List.filter" [l0]) a p l))
(defn cond* [ty b x y] (e/app* (c "cond" [l1]) ty b x y))
(defn eq [ty x y] (e/app* (c "Eq" [l1]) ty x y))

;; ---------------------------------------------------------------------------
;; the laws
;; ---------------------------------------------------------------------------

(def law-map-name "Klara.foldl_map")
(def law-filter-name "Klara.foldl_filter")

(defn- foldl-map-law []
  (let [[A B G f g l b acc x hd tl ih] (repeatedly 12 fvar!)
        [vA vB vG vf vg vl vb vacc vx vhd vtl vih] (map e/fvar [A B G f g l b acc x hd tl ih])
        step (lam* [[acc "acc" vG] [x "x" vA]] (e/app* vf vacc (e/app vg vx)))
        stmt (fn [lv bv] (eq vG (foldl vG vB vf bv (lmap vA vB vg lv)) (foldl vG vA step bv lv)))
        params [[A "α" Type0] [B "β" Type0] [G "γ" Type0]
                [f "f" (arrow vG (arrow vB vG))] [g "g" (arrow vA vB)]]
        motive (lam* [[l "l" (List vA)]] (pi* [[b "b" vG]] (stmt vl vb)))
        nil-case (lam* [[b "b" vG]] (e/app* (c "Eq.refl" [l1]) vG vb))
        cons-case (lam* [[hd "hd" vA] [tl "tl" (List vA)]
                         [ih "ih" (e/app motive vtl)] [b "b" vG]]
                        (e/app vih (e/app* vf vb (e/app vg vhd))))
        proof (lam* (conj params [l "l" (List vA)])
                    (e/app* (c "List.rec" [l0 l0]) vA motive nil-case cons-case vl))
        type (pi* (conj params [l "l" (List vA)] [b "b" vG]) (stmt vl vb))]
    {:name "Klara.foldl_map" :type type :proof proof}))

(defn- foldl-filter-law []
  (let [[A G f p l b acc x hd tl ih cv] (repeatedly 12 fvar!)
        [vA vG vf vp vl vb vacc vx vhd vtl vih vc] (map e/fvar [A G f p l b acc x hd tl ih cv])
        step (lam* [[acc "acc" vG] [x "x" vA]] (cond* vG (e/app vp vx) (e/app* vf vacc vx) vacc))
        stmt (fn [lv bv] (eq vG (foldl vG vA vf bv (lfilter vA vp lv)) (foldl vG vA step bv lv)))
        params [[A "α" Type0] [G "γ" Type0]
                [f "f" (arrow vG (arrow vA vG))] [p "p" (arrow vA Bool)]]
        motive (lam* [[l "l" (List vA)]] (pi* [[b "b" vG]] (stmt vl vb)))
        nil-case (lam* [[b "b" vG]] (e/app* (c "Eq.refl" [l1]) vG vb))
        ;; split on c = p hd; filter p (hd::tl) ≡ cond (p hd) (hd :: filter p tl) (filter p tl)
        ftl (lfilter vA vp vtl)
        split (lam* [[cv "c" Bool]]
                    (eq vG (foldl vG vA vf vb (cond* (List vA) vc
                                                     (e/app* (c "List.cons" [l0]) vA vhd ftl) ftl))
                        (foldl vG vA step (cond* vG vc (e/app* vf vb vhd) vb) vtl)))
        cons-case (lam* [[hd "hd" vA] [tl "tl" (List vA)]
                         [ih "ih" (e/app motive vtl)] [b "b" vG]]
                        (e/app* (c "Bool.rec" [l0]) split
                                (e/app vih vb)                       ; p hd = false
                                (e/app vih (e/app* vf vb vhd))       ; p hd = true
                                (e/app vp vhd)))
        proof (lam* (conj params [l "l" (List vA)])
                    (e/app* (c "List.rec" [l0 l0]) vA motive nil-case cons-case vl))
        type (pi* (conj params [l "l" (List vA)] [b "b" vG]) (stmt vl vb))]
    {:name "Klara.foldl_filter" :type type :proof proof}))

;; ---------------------------------------------------------------------------
;; fingerprints
;; ---------------------------------------------------------------------------

(defn expr-data
  "A canonical data rendering of a kernel Expr (binder names dropped, so
  α-equivalent terms render equally). Used for hashing and comparison."
  [x]
  (cond
    (e/bvar? x) [:b (e/bvar-idx x)]
    (e/fvar? x) [:f (e/fvar-id x)]
    (e/sort? x) [:s (str (e/sort-level x))]
    (e/const? x) [:c (nm/->string (e/const-name x)) (mapv str (e/const-levels x))]
    (e/app? x) [:a (expr-data (e/app-fn x)) (expr-data (e/app-arg x))]
    (e/lam? x) [:l (expr-data (e/lam-type x)) (expr-data (e/lam-body x))]
    (e/forall? x) [:p (expr-data (e/forall-type x)) (expr-data (e/forall-body x))]
    (e/let? x) [:z (expr-data (e/let-type x)) (expr-data (e/let-value x)) (expr-data (e/let-body x))]
    (e/lit-nat? x) [:n (str (e/lit-nat-val x))]
    (e/lit-str? x) [:t (e/lit-str-val x)]
    (e/proj? x) [:j (nm/->string (e/proj-type-name x)) (e/proj-idx x) (expr-data (e/proj-struct x))]
    (e/mdata? x) (expr-data (e/mdata-expr x))
    :else (throw (ex-info "expr-data: unsupported node" {:expr (str x)}))))

(defn expr-hash [x] (kc/sha256 (pr-str (expr-data x))))

(defn constants-of
  "Constant names occurring in expression x."
  [x]
  (let [acc (volatile! #{})]
    (letfn [(walk [x]
              (cond
                (e/const? x) (vswap! acc conj (nm/->string (e/const-name x)))
                (e/app? x) (do (walk (e/app-fn x)) (walk (e/app-arg x)))
                (e/lam? x) (do (walk (e/lam-type x)) (walk (e/lam-body x)))
                (e/forall? x) (do (walk (e/forall-type x)) (walk (e/forall-body x)))
                (e/let? x) (do (walk (e/let-type x)) (walk (e/let-value x)) (walk (e/let-body x)))
                (e/proj? x) (do (vswap! acc conj (nm/->string (e/proj-type-name x)))
                                (walk (e/proj-struct x)))
                (e/mdata? x) (walk (e/mdata-expr x))
                :else nil))]
      (walk x))
    @acc))

(defn decl-hash
  "Fingerprint of declaration n in env: its type, and its value for
  definitions (theorem bodies are irrelevant to users and may be elided
  by stores, so only their statement counts)."
  [^Env en n]
  (when-let [ci (env/lookup en (nm/from-string n))]
    (kc/sha256 (pr-str [(map str (env/ci-level-params ci))
                        (expr-data (env/ci-type ci))
                        (when (and (env/def? ci) (env/ci-value ci))
                          (expr-data (env/ci-value ci)))]))))

(defn closure
  "The dependency closure of the given expressions in env: every
  declaration reachable through types and definition values, as
  {name decl-hash}. Theorems contribute their statements only."
  [^Env en exprs]
  (loop [todo (into [] (mapcat constants-of) exprs) seen {}]
    (if-let [[n & more] (seq todo)]
      (if (contains? seen n)
        (recur (vec more) seen)
        (let [ci (env/lookup en (nm/from-string n))
              deps (when ci (cond-> (constants-of (env/ci-type ci))
                              (and (env/def? ci) (env/ci-value ci))
                              (into (constants-of (env/ci-value ci)))))]
          (recur (into (vec more) deps) (assoc seen n (decl-hash en n)))))
      (into (sorted-map) seen))))

(def checker-version
  "The ansatz release the kernel comes from (from the jar's pom)."
  (delay (or (some->> (io/resource "META-INF/maven/org.replikativ/ansatz/pom.properties")
                      slurp (re-find #"version=(\S+)") second
                      (str "ansatz/"))
             "ansatz/unknown")))

(defn- resource-sha [r]
  (when-let [u (io/resource r)]
    (with-open [in (io/input-stream u)]
      (let [d (java.security.MessageDigest/getInstance "SHA-256")
            buf (byte-array 65536)]
        (loop [] (let [n (.read in buf)] (when (pos? n) (.update d buf 0 n) (recur))))
        (apply str (map #(format "%02x" %) (.digest d)))))))

;; ---------------------------------------------------------------------------
;; the proof environment
;; ---------------------------------------------------------------------------

(defn- load-bundled-env
  "The bundled medium Init tier as an Env value, leaving ansatz's global
  session as it was if one was already active."
  []
  (let [prev @a/ansatz-env]
    (binding [*out* (java.io.StringWriter.)] (a/init!))
    (let [en (a/env)]
      (when prev (reset! a/ansatz-env prev))
      en)))

(defn- admit-law
  "Kernel-check law and add it to en (throws if it does not check)."
  [^Env en {:keys [name type proof]}]
  (env/check-constant en (env/mk-thm (nm/from-string name) [] type proof)))

(def laws [(foldl-map-law) (foldl-filter-law)])

(defonce ^:private state (atom nil))

(defn proof-env
  "{:env Env :cohort {..} :laws {name {:type-hash :proof-hash}}}: the Env
  Klara certifies against, with the laws admitted (each kernel-checked)."
  []
  (or @state
      (let [base (load-bundled-env)
            en (reduce admit-law base laws)
            st {:env en
                :cohort {:source :ansatz/bundled-medium-init
                         :resource "ansatz/init-medium.ndjson.gz"
                         :sha256 (resource-sha "ansatz/init-medium.ndjson.gz")
                         :declarations (.size ^Env base)}
                :laws (into {} (map (fn [{:keys [name type proof]}]
                                      [name {:type-hash (expr-hash type)
                                             :proof-hash (expr-hash proof)}]))
                            laws)}]
        (compare-and-set! state nil st)
        @state)))

(defn env* ^Env [] (:env (proof-env)))

(defn infer
  "The type of closed expression x in the proof env (strict check)."
  [x]
  (.check (doto (TypeChecker. (env*)) (.setFuel 50000000)) x))

(defn verifies?
  "Authoritative: proof kernel-checks as a proof of goal in en."
  [^Env en goal proof]
  (env/verifies? en goal proof))
