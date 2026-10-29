(ns klara.spec-diff-test
  "Differential test (S5): every program in spec/test/klara/spec/programs.edn
  runs through the kernel-checked spec (`klara.spec.core/step`, compiled by
  ansatz) and through T0 (`klara.eval`), and the two observations are
  compared: values, named stuck states, errors.

  Run with `clojure -X:spec-diff`. It is a separate alias because it loads
  the spec (an ansatz elaboration of about 20 s) against the local ansatz
  checkout, while the main suite pins ansatz from Maven.

  Translation. Both paths use the spec front end
  (`klara.spec.interp/parse`) to parse programs into de Bruijn `Tm`; `tm->t0` maps that
  term form by form onto a T0 core term (`klara.core`). Both term languages
  use de Bruijn indices, so the map is index-preserving:

    lam b            {:op :fn :arity 1 :body b}         (curried, as the spec)
    app f x          {:op :app :fn f :args [x]}
    letrec fb b      {:op :letrec :inits [{:op :fn :arity 1 :body fb}] :body b}
    resolve id       {:op :resolve :id sym}
    perform op h x   {:op :perform :target h :name :op :args [x]}
    specialize p m   (((fn [p] (fn [m] (specialize (fn [a y] ((p a) y)) m))) P) M)
    handle b r o     (let [cl (fn [op v k] o)]
                       {:op :handle :mode :lexical :body b'
                        :return (fn [x] r') :clauses {:op_i (specialize cl 'i) ..}})
                     (b', r' shifted past the let)
    code u, esc u    {:op :code ..}, {:op :esc ..}
    run_ u           {:op :perform :target nil :name :stage/run :args [u]}

  The spec has ONE op clause that dispatches on the op tag; T0 dispatches
  by name. The translation gives the T0 handler a clause for every op name
  of the program, each the spec clause partially applied to its tag, so an
  op the source does not handle falls through to the spec's (nil nil) in
  both. A perform whose target evaluates to nil is ambient in both.

  Observations. T0 values: nil/booleans/integers as themselves, closures
  :klara/fn, handler instances :klara/cap, code values as their term
  converted back to the spec's de Bruijn EDN (`t0->edn`, the inverse of
  `tm->t0`). T0 errors are classified by `t0-error` into the spec's stuck
  names. `known-differences` lists the disagreements that are deliberate;
  every other disagreement fails the test."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk]
            [clojure.test :refer [deftest is testing]]
            [klara.code :as code]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.world :as w]
            [klara.spec.interp :as si]))

;; ---------------------------------------------------------------------------
;; spec Tm (ansatz runtime vectors) -> T0 core term

(def ^:private prim-sym {nil '+ 1 '- 2 '* 3 '= 4 '<})

(defn- t0-fn [arity body] {:op :fn :arity arity :rest? false :body body})

(defn shift
  "Add d to every local of T0 term t that points at or past cutoff c."
  [t d c]
  (if (= :local (:op t))
    (if (>= (:index t) c) (update t :index + d) t)
    (let [k (code/binder-arity t)]
      (code/reassemble t (map (fn [[ch under?]] (shift ch d (if under? (+ c k) c))) (code/parts t)) nil))))

(defn tm->t0
  "Translate a source spec Tm (no runtime forms) into a T0 core term.
  ops-inv: op tag -> keyword; ids-inv: world id -> keyword."
  [t {:keys [ops-inv ids-inv] :as tabs}]
  (let [tr #(tm->t0 % tabs)
        [tag & fs] t]
    (case (int tag)
      0 (c/local (long (first fs)))
      1 (c/quote* (si/decode-datum (first fs)))
      2 (t0-fn 1 (tr (first fs)))
      3 (c/app (tr (first fs)) (tr (second fs)))
      4 (c/let1 (tr (first fs)) (tr (second fs)))
      5 (c/if* (tr (nth fs 0)) (tr (nth fs 1)) (tr (nth fs 2)))
      6 (c/letrec [(t0-fn 1 (tr (first fs)))] (tr (second fs)))
      7 (c/resolve* (symbol (name (ids-inv (long (first fs))))))
      8 (c/prim (prim-sym (some-> (first fs) int)) (tr (nth fs 1)) (tr (nth fs 2)))
      9 (c/perform (tr (nth fs 1)) (ops-inv (long (first fs))) (tr (nth fs 2)))
      ;; the clause is let-bound once, so that building it (at level >= 1)
      ;; runs its escs once, as in the spec
      10 (let [[b r o] fs]
           (c/let1 (t0-fn 3 (tr o))
                   (c/handle :lexical
                             (into {} (map (fn [[tg kw]] [kw (c/specialize (c/local 0) (c/quote* tg))])) ops-inv)
                             (t0-fn 1 (shift (tr r) 1 1))
                             (shift (tr b) 1 1))))
      ;; the spec's specialize is curried, ((p m) y); T0's partial application
      ;; calls (p m y) with two arguments. An adapter uncurries:
      ;; (((fn [p] (fn [m] (specialize (fn [a y] ((p a) y)) m))) P) M)
      11 (c/app (c/app (t0-fn 1 (t0-fn 1 (c/specialize
                                          (t0-fn 2 (c/app (c/app (c/local 3) (c/local 1)) (c/local 0)))
                                          (c/local 0))))
                       (tr (first fs)))
                (tr (second fs)))
      15 (c/code* (tr (first fs)))
      16 (c/esc (tr (first fs)))
      17 (c/perform nil :stage/run (tr (first fs)))
      (throw (ex-info "tm->t0: runtime form in a source program" {:tm t})))))

;; ---------------------------------------------------------------------------
;; T0 core term -> spec de Bruijn EDN (for generated code)

(defn t0->edn
  "Inverse of tm->t0 on the image, producing klara.spec.interp/tm->edn's
  format. Opaque cross-stage constants become [:lit :klara/csp]."
  [t {:keys [ops ids] :as tabs}]
  (let [tr #(t0->edn % tabs)]
    (case (:op t)
      :local [:var (:index t)]
      :quote (if (or (:csp t) (fn? (:datum t)) (ev/closure? (:datum t)))
               [:lit :klara/csp]
               [:lit (:datum t)])
      :fn (case (:arity t)
            1 [:lam (tr (:body t))]
            [:t0-fn (:arity t) (tr (:body t))])
      :app (into [:app (tr (:fn t))] (map tr (:args t)))
      :let (let [{:keys [init body]} t]
             (if (and (= :fn (:op init)) (= 3 (:arity init)) (= :handle (:op body))
                      (every? #(= (:op %) :specialize) (vals (:clauses body))))
               ;; the image of a spec handle (see tm->t0)
               [:handle (tr (shift (:body body) -1 1)) (tr (shift (:body (:return body)) -1 1))
                (tr (:body init))]
               [:let (tr init) (tr body)]))
      :if [:if (tr (:test t)) (tr (:then t)) (tr (:else t))]
      :letrec (let [[f & more] (:inits t)]
                (if (and (empty? more) (= 1 (:arity f)))
                  [:letrec (tr (:body f)) (tr (:body t))]
                  [:t0-letrec (mapv tr (:inits t)) (tr (:body t))]))
      :resolve [:resolve (get ids (keyword (name (:id t))) (:id t))]
      :prim (into [:prim (:name t)] (map tr (:args t)))
      :perform (if (:target t)
                 (into [:perform (get ops (:name t) (:name t)) (tr (:target t))] (map tr (:args t)))
                 (if (= :stage/run (:name t))
                   [:run (tr (first (:args t)))]
                   (into [:perform-ambient (:name t)] (map tr (:args t)))))
      :handle [:t0-handle (tr (:body t))]
      :specialize (into [:specialize (tr (:fn t))] (map tr (:args t)))
      :code [:code (tr (:body t))]
      :esc [:esc (tr (:body t))])))

(defn- spec-normalize
  "The spec keeps a recursive closure that persists into code as `fix`;
  T0 makes it an opaque constant. Both observe as [:lit :klara/csp]."
  [x]
  (clojure.walk/postwalk (fn [y] (if (and (vector? y) (= :fix (first y))) [:lit :klara/csp] y)) x))

;; ---------------------------------------------------------------------------
;; running T0 and observing

(defn- t0-world
  "A T0 root holding the program's world: each value term is evaluated
  under the empty root and published as a raw definition."
  [world tabs]
  (reduce (fn [root [id form]]
            (let [{:keys [tm]} (si/parse form)
                  v (ev/run (tm->t0 tm tabs) {:basis w/empty-root :mint nil})]
              (w/put-entry root (symbol (name id))
                           {:kind :def :value v :reads #{} :code-id (str "diff:" id)
                            :value-id (str "diff:" id)})))
          w/empty-root (sort-by key world)))

(defn- t0-value [v tabs]
  (cond
    (or (nil? v) (boolean? v) (integer? v)) v
    (or (ev/closure? v) (ev/pap? v)) :klara/fn
    (code/code? v) (let [t (try (code/s->core (code/code-term v)) (catch clojure.lang.ExceptionInfo _ nil))]
                     (if t {:klara/code (t0->edn t tabs)} :klara/open-code))
    (= "klara.eval.Instance" (.getName (class v))) :klara/cap
    :else {:klara/host (pr-str v)}))

(defn t0-error
  "Classify a T0 error as a spec stuck state."
  [^Throwable e]
  (let [msg (or (.getMessage e) "")
        d (ex-data e)
        kind (:klara/error d)
        first-wf (some-> d :errors first :error)]
    (cond
      (= :scope-extrusion kind) {:stuck :scope-extrusion}
      (= :lift kind) {:stuck :lift}
      (= :stage kind) {:stuck :stage}
      (and first-wf (= "esc outside code" first-wf)) {:stuck :stage}
      (str/starts-with? msg "klara: not a function") {:stuck :not-fn}
      (str/starts-with? msg "klara: unhandled lexical effect") {:stuck :unhandled-instance :op (:op d)}
      (str/starts-with? msg "klara: no handler for") {:stuck :unhandled-op :op (:op d)}
      (str/starts-with? msg "klara: unbound") {:stuck :unbound :id (keyword (name (:sym d)))}
      (or (instance? ClassCastException e) (instance? NullPointerException e)
          (instance? ArithmeticException e))
      {:stuck :prim-type}
      :else {:t0-error (.getName (class e)) :message msg})))

(defn run-t0 [{:keys [program world]}]
  (let [{:keys [tm ops ids]} (si/parse program (or world {}))
        tabs {:ops ops :ids ids
              :ops-inv (zipmap (vals ops) (keys ops))
              :ids-inv (zipmap (vals ids) (keys ids))}
        root (t0-world (or world {}) tabs)
        t (tm->t0 tm tabs)]
    (try {:value (t0-value (ev/run t {:basis root}) tabs)}
         (catch Throwable e (t0-error e)))))

(defn run-spec [{:keys [program world]}]
  (spec-normalize (dissoc (si/run program (or world {})) :steps)))

;; ---------------------------------------------------------------------------
;; the corpus

(defn load-programs []
  (edn/read-string (slurp (io/file "spec/test/klara/spec/programs.edn"))))

(def known-differences
  "Program name -> why spec and T0 deliberately disagree.
  See the observation boundary in doc/interpreters.md."
  {:bad-perform-target
   "T0 reports a perform on a non-instance as 'unhandled lexical effect'; the spec names it :bad-target"
   :csp-code-value
   "a code value used at level 1 without esc: T0 refuses it (stage error); the spec substitutes it, a nested quotation"
   :csp-closure-over-code-var
   "a closure that captures a generated variable, used at level 1: T0 refuses to lift it; the spec substitutes it and re-reads the variable at level 1"
   :eq-on-code
   "T0's = is clojure.core/= on any values; the spec's = is defined on datums only (:prim-type otherwise)"})

(defn in-fragment?
  "Programs whose op names fall in an ambient namespace of klara.core
  (world host exn time stage auth) are outside the formal fragment: the
  spec has no ambient operations except as unhandled `perform nil`, and
  the authority operations of S6 (`:auth/*`) are not modelled."
  [{:keys [program]}]
  (not-any? #(and (keyword? %) (c/ambient? %)) (tree-seq coll? seq program)))

(defn compare-all []
  (vec (for [p (load-programs) :when (in-fragment? p)]
         (let [s (run-spec p) t (run-t0 p)]
           {:name (:name p) :spec s :t0 t :expect (:expect p)
            :agree (= s t) :known (known-differences (:name p))}))))

(deftest spec-vs-t0
  (let [rs (compare-all)]
    (doseq [{:keys [name spec t0 expect agree known]} rs]
      (testing (str name)
        (is (= (spec-normalize expect) spec) "the spec matches the recorded expectation")
        (if known
          (is (not agree) (str "known difference no longer differs: " known))
          (is agree (str "spec " (pr-str spec) " vs T0 " (pr-str t0))))))
    (println (count rs) "programs;" (count (filter :agree rs)) "agree;"
             (count (filter :known rs)) "known differences")))
