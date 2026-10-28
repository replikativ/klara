(ns klara.fusion-test
  "S3 end to end: define a pipeline, claim its shape, optimize it into a
  certified fused executable, compare with generic on random inputs, edit
  a stage (immediate generic fallback, re-certification), delete the cache
  (R3), reject forged certificates, and run the same pipelines in wandler
  (differential)."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [klara.fusion :as f]
            [klara.fusion.kernel :as k]
            [klara.stage :as s]
            [klara.world :as w]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(def claim '{:args [(List Nat)] :ret Nat})

;; [name klara-definition-body] — the same body is the wandler source
(def pipelines
  '[[sum-sq-even (fn [xs] (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (even? x)) xs))))]
    [count-big (fn [xs] (reduce (fn [acc x] (+ acc 1)) 0 (filter (fn [x] (< 10 x)) xs)))]
    [four-stage (fn [xs] (reduce + 0 (filter (fn [x] (< x 200)) (map (fn [x] (* x 3))
                                                                   (filter (fn [x] (odd? x)) (map (fn [x] (+ x 1)) xs))))))]
    [plain-sum (fn [xs] (reduce + xs))]
    [prod-small (fn [xs] (reduce * (map (fn [x] (inc (rem x 3))) xs)))]
    [cond-map (fn [xs] (reduce + 7 (map (fn [x] (if (and (pos? x) (<= x 50)) (quot x 2) (* 2 x))) xs)))]])

(defn session-with [defs]
  (let [S (f/session)]
    (doseq [[n body] defs]
      (f/define! S (list 'def n body))
      (f/claim! S n claim))
    S))

(defn- outcome [thunk]
  (try [:ok (thunk)] (catch Throwable t [:throw (class t)])))

(defn- rand-input [^java.util.Random r]
  (let [n (.nextInt r 40)
        big? (zero? (.nextInt r 5))]
    (vec (repeatedly n #(if big?
                          (- Long/MAX_VALUE (long (.nextInt r 1000)))  ; overflow region
                          (long (.nextInt r 100)))))))

(deftest laws-are-kernel-checked
  (let [{:keys [env]} (k/proof-env)]
    (doseq [{:keys [name type proof]} k/laws]
      (is (env/lookup env (nm/from-string name)) (str name " admitted"))
      (is (k/verifies? env type proof)))
    (testing "a wrong statement is rejected: the filter law with cond's branches swapped"
      (let [{:keys [type proof]} (second k/laws)
            swap (fn swap [x]
                   (cond
                     (and (e/app? x) (let [[h as] (e/get-app-fn-args x)]
                                       (and (e/const? h) (= "cond" (nm/->string (e/const-name h)))
                                            (= 4 (count as)))))
                     (let [[h [t c a b]] (e/get-app-fn-args x)] (e/app* h t c b a))
                     (e/app? x) (e/app (swap (e/app-fn x)) (swap (e/app-arg x)))
                     (e/lam? x) (e/lam (e/lam-name x) (swap (e/lam-type x)) (swap (e/lam-body x)) :default)
                     (e/forall? x) (e/forall' (e/forall-name x) (swap (e/forall-type x)) (swap (e/forall-body x)) :default)
                     :else x))]
        (is (not (k/verifies? env (swap type) proof)))))))

(deftest a-la-carte-and-opaque-stages
  (let [S (f/session)]
    (f/define! S '(def p (fn [xs] (reduce + 0 (map (fn [x] (* x x)) xs)))))
    (is (= {:status :generic :reason :no-shape-claim} (f/optimize! S 'p)) "unclaimed stays generic")
    (is (empty? (s/executables (:cache S))))
    (f/define! S '(def q (fn [xs] (reduce + 0 (map (fn [x] (dec x)) xs)))))
    (f/claim! S 'q claim)
    (is (= [:opaque-stage 0 :map [:prim 'dec]] (:reason (f/optimize! S 'q)))
        "dec: Nat subtraction truncates, longs do not")
    (f/define! S '(def noisy (fn [x] (do (println x) (even? x)))))
    (f/define! S '(def r (fn [xs] (reduce + 0 (filter noisy xs)))))
    (f/claim! S 'r claim)
    (is (= :opaque-stage (first (:reason (f/optimize! S 'r)))) "an effectful stage blocks fusion")
    (f/define! S '(def loopy (fn [x] (if (zero? x) true (loopy x)))))
    (f/define! S '(def t (fn [xs] (reduce + 0 (filter loopy xs)))))
    (f/claim! S 't claim)
    (is (= [:opaque-stage 0 :filter [:recursive 'loopy]] (:reason (f/optimize! S 't))))
    (is (empty? (s/executables (:cache S))))
    (is (= 0 (f/run S '(r [1 3]))) "and the generic path still runs")))

(deftest fused-equals-generic-on-random-inputs
  (let [S (session-with pipelines)
        r (java.util.Random. 20261027)]
    (doseq [[n] pipelines]
      (let [rep (f/optimize! S n)]
        (is (= :fused (:status rep)) (str n))
        (is (= 1 (count (filter #(= :reduce %) (:stages rep)))))))
    (dotimes [_ 300]
      (let [xs (rand-input r)]
        (doseq [[n] pipelines]
          (let [form (list n xs)]
            (is (= (outcome #(f/run-generic S form)) (outcome #(f/run S form)))
                (str n " " (pr-str (take 3 xs))))))))
    (let [st (s/stats (:cache S))
          deopts (reduce + (map (comp deref :deopts) (s/executables (:cache S))))]
      (is (pos? (:hits st)))
      (is (pos? deopts) "overflowing inputs declined to generic"))
    (testing "entry guards: non-Nat inputs and lazy seqs run generic"
      (let [before (:fallbacks (s/stats (:cache S)))]
        (doseq [xs ['[1 -2 3] '[1.5 2] '(range 5) '(map inc [1 2]) nil '[]]]
          (is (= (outcome #(f/run-generic S (list 'sum-sq-even xs)))
                 (outcome #(f/run S (list 'sum-sq-even xs))))))
        (is (= (+ before 4) (:fallbacks (s/stats (:cache S)))) "nil and [] are (List Nat)")))
    (testing "a dynamic handler of :host/call around the call: generic runs"
      (let [form '(handle :dynamic {:host/call (fn [sym & as] ((last as) 42))} (sum-sq-even [2 4]))
            hits (:hits (s/stats (:cache S)))]
        (is (= 42 (f/run-generic S form)))
        (is (= 42 (f/run S form)))
        (is (= hits (:hits (s/stats (:cache S)))))))))

(deftest edit-a-stage-then-reoptimize
  (let [S (f/session)]
    (f/define! S '(def keep? (fn [x] (even? x))))
    (f/define! S '(def p (fn [xs] (reduce + 0 (map (fn [x] (* x x)) (filter keep? xs))))))
    (f/claim! S 'p claim)
    (let [r1 (f/optimize! S 'p)
          xs [1 2 3 4 5 6]]
      (is (= :fused (:status r1)))
      (is (= 56 (f/run S (list 'p xs))))
      (is (= 1 (:hits (s/stats (:cache S)))))
      (testing "edit the filter predicate: the next call is generic"
        (f/define! S '(def keep? (fn [x] (odd? x))))
        (is (= 35 (f/run-generic S (list 'p xs))))
        (is (= 35 (f/run S (list 'p xs))) "immediately the new predicate")
        (is (= {:hits 1 :fallbacks 1} (select-keys (s/stats (:cache S)) [:hits :fallbacks]))))
      (testing "re-optimize: a new certified executable"
        (let [r2 (f/optimize! S 'p)]
          (is (= :fused (:status r2)))
          (is (= (:code-id r1) (:code-id r2)) "same Klara code")
          (is (not= (:theorem r1) (:theorem r2)) "a different theorem")
          (is (not= (:guards r1) (:guards r2)))
          (is (= 35 (f/run S (list 'p xs))))
          (is (= 2 (:hits (s/stats (:cache S)))))
          (is (= 1 (s/invalidate! (:cache S) (w/snapshot (:world S)))) "the sweep drops the old one")
          (is (= 1 (count (s/executables (:cache S)))))))
      (testing "edit the pipeline itself: new CodeId, generic until re-optimized"
        (f/define! S '(def p (fn [xs] (reduce + 1 (map (fn [x] (* x x)) (filter keep? xs))))))
        (is (= 36 (f/run S (list 'p xs))))
        (is (= :fused (:status (f/optimize! S 'p))))
        (is (= 36 (f/run S (list 'p xs))))
        (is (= 3 (:hits (s/stats (:cache S))))))
      (testing "edit the claim: the guard on p$shape fails"
        (f/claim! S 'p '{:args [(List Nat)] :ret Int})
        (let [h (:hits (s/stats (:cache S)))]
          (is (= 36 (f/run S (list 'p xs))))
          (is (= h (:hits (s/stats (:cache S)))))
          (is (= :generic (:status (f/optimize! S 'p)))))))))

(deftest r3-deleting-the-cache-changes-nothing
  (let [S (session-with pipelines)
        r (java.util.Random. 7)
        inputs (vec (repeatedly 50 #(rand-input r)))
        forms (for [[n] pipelines xs inputs] (list n xs))
        generic (mapv #(outcome (fn [] (f/run-generic S %))) forms)]
    (doseq [[n] pipelines] (f/optimize! S n))
    (is (= generic (mapv #(outcome (fn [] (f/run S %))) forms)))
    (is (pos? (:hits (s/stats (:cache S)))))
    (s/clear! (:cache S))
    (is (= generic (mapv #(outcome (fn [] (f/run S %))) forms)))))

(deftest install-rejects-forged-certificates
  (let [S (session-with pipelines)
        root (w/snapshot (:world S))
        exe (:executable (f/specialize root 'sum-sq-even))
        other (:executable (f/specialize root 'count-big))
        reason (fn [exe] (try (s/install! (s/make-cache) exe) :installed
                              (catch Exception ex (:reason (ex-data ex)))))
        reseal (fn [exe] (update exe :certificate #(assoc % :digest (s/digest %))))]
    (is (= :installed (reason exe)))
    (is (= :digest-mismatch (reason (assoc-in exe [:certificate :laws "Klara.foldl_map" :proof-hash] "0"))))
    (is (= :law-mismatch (reason (reseal (assoc-in exe [:certificate :laws "Klara.foldl_map" :proof-hash] "0")))))
    (is (= :cohort-mismatch (reason (reseal (assoc-in exe [:certificate :cohort :sha256] "0")))))
    (is (= :checker-version-mismatch (reason (reseal (assoc-in exe [:certificate :checker-version] "ansatz/0")))))
    (is (= :lowering-mismatch (reason (assoc exe :run (:run other)))) "a host fn not compiled from the form")
    (is (= :lowering-mismatch (reason (assoc exe :form (:form other) :run (:run other)))))
    (is (= :proof-hash-mismatch
           (reason (assoc-in exe [:certificate :payload :proof] (get-in other [:certificate :payload :proof])))))
    (testing "a self-consistent certificate whose proof does not prove the goal"
      (let [bogus (get-in other [:certificate :payload :proof])
            forged (-> exe
                       (assoc-in [:certificate :payload :proof] bogus)
                       (assoc-in [:certificate :theorem :proof-hash] (k/expr-hash bogus))
                       (assoc-in [:certificate :closure]
                                 (k/closure (k/env*) [(get-in exe [:certificate :payload :goal]) bogus]))
                       reseal)]
        (is (= :proof-rejected (reason forged)))))
    (testing "a certificate claiming a different source"
      (is (= :source-mismatch
             (reason (reseal (assoc-in exe [:certificate :source] (get-in other [:certificate :source]))))))
      (is (= :stage-mismatch
             (reason (reseal (assoc-in exe [:certificate :source :stages 'sum-sq-even$shape :value-id] "0"))))))))

;; ---------------------------------------------------------------------------
;; differential check against wandler (needs the full Init export)
;; ---------------------------------------------------------------------------

(def init-ndjson "../wandler/test-data/init.ndjson")

(def wandler-env
  (delay
    (when (.exists (io/file init-ndjson))
      (let [parse (requiring-resolve 'ansatz.export.parser/parse-ndjson-file)
            replay (requiring-resolve 'ansatz.export.replay/replay)
            bundled (requiring-resolve 'ansatz.tactic.instance/load-bundled-instances)
            ke (:env (replay (:decls (parse init-ndjson)) :verify? false))]
        (env/with-extension ke :instances
          (bundled {:present? #(some? (env/lookup ke (nm/from-string %)))}))))))

(defn wandler-define!
  "Define pipeline n in wandler (a/defn over (List Nat) -> Nat); returns
  [fn explain]. Requires @wandler-env."
  [n body]
  (k/proof-env)                         ; Klara's env is captured before the switch
  (reset! @(requiring-resolve 'ansatz.core/ansatz-env) @wandler-env)
  ((requiring-resolve 'wandler.core/install!))
  (let [wn (symbol (str "w-" n))
        [_ params & bd] body]
    (binding [*ns* (the-ns 'klara.fusion-test)]
      (eval (list 'binding ['ansatz.core/*verbose* false]
                  (list* 'ansatz.core/defn wn [(first params) :- '(List Nat)] 'Nat bd))))
    [@(ns-resolve 'klara.fusion-test wn) ((requiring-resolve 'wandler.core/explain) wn)]))

(def wandler-overrides
  "Wandler sources where its surface differs (doc/impl/S3.md §7): it does
  not elaborate reduce without init (a kernel type error on an mvar, not a
  clean rejection) and has no pos?. Same function, other spelling."
  '{plain-sum (fn [xs] (reduce + 0 xs))
    prod-small (fn [xs] (reduce * 1 (map (fn [x] (inc (rem x 3))) xs)))
    cond-map (fn [xs] (reduce + 7 (map (fn [x] (if (and (< 0 x) (<= x 50)) (quot x 2) (* 2 x))) xs)))})

(deftest differential-against-wandler
  (if-not @wandler-env
    (is true "skipped: no ../wandler/test-data/init.ndjson")
    (let [S (session-with pipelines)
          r (java.util.Random. 99)]
      (doseq [[n] pipelines] (is (= :fused (:status (f/optimize! S n)))))
      (doseq [[n body] pipelines]
        (let [[wf ex] (wandler-define! n (get wandler-overrides n body))]
          (is (:verified? ex) (str "wandler certified " n))
          (dotimes [_ 100]
            (let [xs (vec (repeatedly (.nextInt r 30) #(long (.nextInt r 100))))
                  kl (f/run S (list n xs))]
              (is (== kl (wf xs)) (str n " " xs))
              (is (= kl (f/run-generic S (list n xs)))))))))))
