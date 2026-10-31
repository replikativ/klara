(ns proof-staging
  "Experimental proof-licensed edges between actual staged Code values.
   Restricted to closed pure Nat map/reduce terms; no runtime cache installer.
   The mathematical proof is checked. Elaboration, interval analysis, and T0
   correspondence remain trusted/tested bridges. See README.md."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [clojure.java.io :as io]
            [klara.code :as code]
            [klara.core :as core]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.fusion :as fusion]
            [klara.fusion.kernel :as k]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn prove-laws!
  "Capture an immutable environment after checking our four new proofs.
   Imported Init statements are trusted by default, as recorded in the report."
  []
  (a/init!)
  (swap! a/ansatz-env
         #(reduce (fn [en {:keys [name type proof]}]
                    (env/check-constant en (env/mk-thm (nm/from-string name) [] type proof)))
                  % k/laws))
  (a/theorem KlaraExperiment.horner
    [a :- Nat, b :- Nat, c :- Nat, x :- Nat]
    (= Nat (+ a (+ (* x b) (* (* x x) c)))
           (+ a (* x (+ b (* x c)))))
    (rw Nat.mul_assoc) (rw Nat.left_distrib))
  ;; A second proof uses selected lemma instances as e-graph facts.
  ;; Search discovers congruence/transitivity; the final proof is kernel checked.
  (a/theorem KlaraExperiment.horner-grind
    [a :- Nat, b :- Nat, c :- Nat, x :- Nat]
    (= Nat (+ a (+ (* x b) (* (* x x) c)))
           (+ a (* x (+ b (* x c)))))
    (have ha (= (* (* x x) c) (* x (* x c))) (Nat.mul_assoc x x c))
    (have hd (= (* x (+ b (* x c))) (+ (* x b) (* x (* x c))))
          (Nat.left_distrib x b (* x c)))
    (grind))
  (a/theorem KlaraExperiment.horner-function
    [a :- Nat, b :- Nat, c :- Nat]
    (= (=> Nat Nat)
       (fn [x :- Nat] (+ a (+ (* x b) (* (* x x) c))))
       (fn [x :- Nat] (+ a (* x (+ b (* x c))))))
    (funext x) (exact (KlaraExperiment.horner a b c x)))
  (a/theorem KlaraExperiment.horner-map-sum
    [a :- Nat, b :- Nat, c :- Nat, xs :- (List Nat)]
    (= Nat
       (List.foldl Nat.add 0
         (List.map (fn [x :- Nat] (+ a (+ (* x b) (* (* x x) c)))) xs))
       (List.foldl Nat.add 0
         (List.map (fn [x :- Nat] (+ a (* x (+ b (* x c))))) xs)))
    (rw (KlaraExperiment.horner-function a b c)))
  (a/theorem KlaraExperiment.horner-fold-step
    [a :- Nat, b :- Nat, c :- Nat]
    (= (=> Nat (=> Nat Nat))
       (fn [acc :- Nat, x :- Nat] (+ acc (+ a (+ (* x b) (* (* x x) c)))))
       (fn [acc :- Nat, x :- Nat] (+ acc (+ a (* x (+ b (* x c)))))))
    (funext acc) (funext x)
    (exact (congrArg (fn [v :- Nat] (+ acc v)) (KlaraExperiment.horner a b c x))))
  (a/theorem KlaraExperiment.horner-fold-sum
    [a :- Nat, b :- Nat, c :- Nat, xs :- (List Nat)]
    (= Nat
       (List.foldl (fn [acc :- Nat, x :- Nat] (+ acc (+ a (+ (* x b) (* (* x x) c))))) 0 xs)
       (List.foldl (fn [acc :- Nat, x :- Nat] (+ acc (+ a (* x (+ b (* x c)))))) 0 xs))
    (rw (KlaraExperiment.horner-fold-step a b c)))
  (a/env))

(defonce proof-state (delay (prove-laws!)))

;; Proof proposals are ordinary data; accepted edges are opaque to Klara.
;; As with Prepared, arbitrary host reflection/constructors are outside the
;; boundary. No assoc operation can silently change an accepted endpoint.
(deftype CheckedEdge [data]
  clojure.lang.ILookup
  (valAt [_ key] (get data key))
  (valAt [_ key missing] (get data key missing)))

(defmethod print-method CheckedEdge [_ out]
  (.write ^java.io.Writer out "#<checked-mathematical-edge>"))

(defn- require-edge! [edge]
  (when-not (instance? CheckedEdge edge)
    (throw (ex-info "expected a checker-issued edge" {:reason :unchecked}))))

(defn proposals [coefficients]
  (let [wo (w/make-world)]
    (with-open [r (java.io.PushbackReader.
                    (io/reader "experiments/proof_staging/polynomial.klr"))]
      (doseq [form (take-while #(not= ::end %)
                             (repeatedly #(read {:eof ::end} r)))]
        (d/define! wo form)))
    (d/eval-form (w/snapshot wo) (cons 'polynomial-proposals coefficients))))

(defn core-term [c]
  (when-not (and (code/code? c) (code/closed? c))
    (throw (ex-info "edge requires closed staged code" {:reason :scope})))
  (code/s->core (code/code-term c)))

(defn meaning
  "Re-elaborate the actual Code endpoint, not a claimed expression/hash."
  [c xs]
  (let [el (fusion/elaborate {:claim fusion/supported-claim :resolve-def (constantly nil)}
                           (core-term c))]
    (when (some #(not= :map (first %)) (:chain el))
      (throw (ex-info "experiment only accepts maps and a fold" {})))
    (:naive (fusion/fuse (assoc el :xs xs)))))

(defn goal [from to xs]
  (k/pi* [[xs "xs" (k/List k/Nat)]]
         (k/eq k/Nat (meaning from xs) (meaning to xs))))

(defn- bound-expr
  "Conservative upper bounds for every intermediate, in arbitrary precision.
   Only monotone nonnegative + and * are admitted, no zero-factor shortcut."
  [term locals]
  (case (:op term)
    :local (nth locals (- (count locals) 1 (:index term)))
    :quote (let [n (:datum term)]
             (when-not (and (instance? Long n) (<= 0 n))
               (throw (ex-info "non-Nat Long literal" {})))
             (bigint n))
    :prim (let [bs (mapv #(bound-expr % locals) (:args term))
                [op unit] (case (:name term)
                            + [+' 0N]
                            * [*' 1N]
                            (throw (ex-info "unsupported bound operation" {})))]
            ;; Check partial n-ary results too: (* x x 0) may overflow before
            ;; reaching zero, even though its final mathematical bound is zero.
            (reduce (fn [a b]
                      (let [n (op a b)]
                        (when (> n Long/MAX_VALUE)
                          (throw (ex-info "intermediate may overflow"
                                          {:reason :overflow :bound n})))
                        n)) unit bs))
    (throw (ex-info "unsupported bound term" {:op (:op term)}))))

(defn- interval-check!
  "Check each AST operation and the total fold bound. The final fold must
   be addition, and at most one pure map is allowed. This bridge is not proved."
  [c {:keys [max-x max-count]}]
  (when-not (and (instance? Long max-x) (<= 0 max-x)
                 (instance? Long max-count) (<= 0 max-count))
    (throw (ex-info "invalid bounded domain" {})))
  (let [term (core-term c)
        _ (meaning c (k/fvar!))
        [_ f init src] (get-in term [:body :args])
        zero? (= {:op :quote :datum 0} init)
        mapped? (= :perform (:op src))
        polynomial (if mapped?
                     (get-in src [:args 1 :body])
                     (get-in f [:body :args 1]))
        plus? (if mapped?
                (= 'clojure.core/+ (get-in f [:args 0 :datum]))
                (and (= :fn (:op f)) (= 2 (:arity f))
                     (= :prim (get-in f [:body :op]))
                     (= '+ (get-in f [:body :name]))
                     (= 2 (count (get-in f [:body :args])))
                     (= {:op :local :index 1} (get-in f [:body :args 0]))))
        source (if mapped? (get-in src [:args 2]) src)]
    (when-not (and zero? plus? (= {:op :local :index 0} source))
      (throw (ex-info "bound checker requires sum of one polynomial" {})))
    (let [b (bound-expr polynomial (if mapped? [nil (bigint max-x)] [nil nil (bigint max-x)]))
          total (*' b max-count)]
      (when (> total Long/MAX_VALUE)
        (throw (ex-info "fold may overflow" {:reason :overflow :bound total})))
      {:element b :sum total})))

(defn polynomial-body
  "Actual scalar endpoint inspected by interval-check!, after validating the
   supported map/fold shape. Used by the consolidation proof-producing bound
   adapter; source-to-theory correspondence remains an explicit bridge."
  [source domain]
  (interval-check! source domain)
  (let [term (core-term source)
        [_ f _ src] (get-in term [:body :args])]
    (if (= :perform (:op src)) (get-in src [:args 1 :body])
        (get-in f [:body :args 1]))))

(declare ^:private require-reference-roots!)

(defn checked-edge [from to proof domain]
  (require-reference-roots!)
  (let [xs (k/fvar!) g (goal from to xs) en @proof-state]
    (when-not (k/verifies? en g proof)
      (throw (ex-info "proof does not license these staged endpoints" {:reason :proof})))
    (CheckedEdge.
      {:from from :to to :proof proof :goal g :domain domain
       :bounds [(interval-check! from domain) (interval-check! to domain)]
       :source-id (core/code-id (core-term from))
       :target-id (core/code-id (core-term to))})))

(defn numeric-edge [from to coefficients domain]
  (let [xs (k/fvar!)
        el (fusion/elaborate {:claim fusion/supported-claim :resolve-def (constantly nil)} (core-term from))
        law (if (empty? (:chain el)) "KlaraExperiment.horner-fold-sum" "KlaraExperiment.horner-map-sum")
        p (apply e/app* (k/c law)
                 (concat (map #(e/lit-nat (biginteger %)) coefficients) [(e/fvar xs)]))]
    (checked-edge from to (k/lam* [[xs "xs" (k/List k/Nat)]] p) domain)))

(defn fusion-edge [from to domain]
  (let [el (fusion/elaborate {:claim fusion/supported-claim :resolve-def (constantly nil)}
                           (core-term from))]
    (checked-edge from to (:proof (fusion/fuse el)) domain)))

(defn compose
  "Sequential obligation: exact intermediate code identity; intersect
   domains; build Eq.trans and recheck the complete source/target proposition."
  [left right]
  (require-edge! left)
  (require-edge! right)
  (when-not (= (core-term (:to left)) (core-term (:from right)))
    (throw (ex-info "edge endpoints do not match" {:reason :composition})))
  (let [xs (k/fvar!) v (e/fvar xs)
        a (meaning (:from left) xs) b (meaning (:to left) xs) c (meaning (:to right) xs)
        p (e/app* (k/c "Eq.trans" [k/l1]) k/Nat a b c
                  (e/app (:proof left) v) (e/app (:proof right) v))
        domain (merge-with min (:domain left) (:domain right))]
    (checked-edge (:from left) (:to right)
                  (k/lam* [[xs "xs" (k/List k/Nat)]] p) domain)))

(defonce reference-host-roots
  [[:host-root 'clojure.core/map @#'clojure.core/map]
   [:host-root 'clojure.core/reduce @#'clojure.core/reduce]
   [:host-root 'clojure.core/+ @#'clojure.core/+]
   [:host-root 'klara.core/prims @#'core/prims]])

(defn- reference-roots? []
  (every? #(stage/guard-holds? % {}) reference-host-roots))

(defn- require-reference-roots! []
  (when-not (reference-roots?)
    (throw (ex-info "experiment requires reference Clojure primitive roots"
                    {:reason :host-roots}))))

(defn- reference-context? []
  (stage/guard-holds? [:unhandled #{:host/call :host/var :exn/raise}]
                      {:kont (mapcat identity ev/*outer-k*)}))

(defn admitted? [edge xs]
  (require-edge! edge)
  (and (reference-roots?) (reference-context?)
       (= clojure.lang.PersistentVector (class xs))
       (<= (count xs) (get-in edge [:domain :max-count]))
       (every? #(and (instance? Long %) (<= 0 % (get-in edge [:domain :max-x]))) xs)))

(defn select
  "Sum/alternative obligation: every candidate has the same source. Costs are
   advisory proposer data; only a checked edge whose domain holds is eligible.
   Intended for the isolated host harness, outside active Klara handlers."
  [source edges xs]
  ;; Check before any endpoint traversal: that traversal itself uses map/reduce.
  (require-reference-roots!)
  (doseq [edge edges]
    (require-edge! edge)
    (when-not (= (core-term source) (core-term (:from edge)))
      (throw (ex-info "alternatives require one source" {:reason :alternatives}))))
  (first (filter #(admitted? % xs) edges)))

(defn run-code [c xs]
  (ev/call-value (ev/run (core-term c) {:basis w/empty-root}) [xs]))

(defn run-selected [source edges xs]
  (require-reference-roots!)
  (when-not (reference-context?)
    (throw (ex-info "experiment requires reference host/exception handlers"
                    {:reason :active-handler})))
  (if-let [edge (select source edges xs)]
    (run-code (:to edge) xs)
    (run-code source xs)))
