(ns klara.compositional-analysis-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.analysis :as analysis]
            [klara.compile.infer-affine :as ia]
            [klara.compile.affine-erase :as erase]
            [klara.compile.staged :as staged]
            [klara.authority :as a]
            [klara.code :as code]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.infer-affine-test :as base]
            [klara.stage :as stage]
            [klara.world :as w]))

(def step '(fn [a] (assoc a 0 (inc (nth a 0)))))
(def wrapped '(fn [a] [a]))
(def kernel '(fn [n]
               (let [step step]
                 (loop [i 0 acc [0]]
                   (if (< i n) (recur (inc i) (step acc)) acc)))))
(defn source [root form] (d/eval-form root (list 'code form)))
(defn term [src] (code/s->core (code/code-term src)))
(defn call [root src args] (ev/call-value (ev/run (term src) {:basis root}) args))
(defn rejection [f]
  (try (f) :accepted
       (catch clojure.lang.ExceptionInfo e (select-keys (ex-data e) [:reason :check]))))

(deftest harmless-alias-and-closed-local-helper
  (doseq [form
          ['(fn [n] (loop [i 0 acc [0]]
                      (let [a acc b a]
                        (if (< i n) (recur (inc i) (assoc b 0 (inc (nth a 0)))) b))))
           '(fn [n] (let [step (fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))]
                      (loop [i 0 acc [0]]
                        (if (< i n) (recur (inc i) (step acc)) acc))))]]
    (let [src (source w/empty-root form) cache (stage/make-cache)
          candidate (ia/prepare w/empty-root src)
          inference (:inference (staged/prepared-info candidate))
          boxed (eval (:form (erase/erase (:owned inference) (:derivation inference)
                                         {:in-place? false})))]
      (is (seq (get-in inference [:analysis :rules])))
      (is (= :installed (:status (staged/install! cache w/empty-root candidate))))
      (doseq [n [-1 0 1 2 20 100]]
        (let [expected (call w/empty-root src [n])]
          (is (= expected (boxed n)))
          (is (= expected (stage/with-cache cache (call w/empty-root src [n])))))))))

(deftest summaries-distinguish-retention-from-writes
  (let [a (analysis/summarize (term (source w/empty-root step)))
        b (analysis/summarize (term (source w/empty-root wrapped)))]
    (is (= #{} (:retained-arguments a)))
    (is (= #{[:long-vector 0]} (:requirements a)))
    (is (= #{0} (:retained-arguments b)))
    (is (= (:effects a) (:effects b)))
    (is (= a (analysis/summarize (:source a)))))
  (let [identity-through-wrapper '(fn [a] (nth (if true [a] [a]) 0))
        summary (analysis/summarize (term (source w/empty-root identity-through-wrapper)))]
    (is (= #{0} (:retained-arguments summary)))))

(deftest retaining-results-decline-at-the-summary-boundary
  (doseq [helper [wrapped '(fn [a] (if true [a] [0]))
                  '(fn [a] (if true [0] [a]))]]
    (let [wo (w/make-world)]
      (d/define! wo (list 'def 'step helper))
      (let [root (w/snapshot wo) src (source root kernel)]
        (is (= {:reason :unsupported-region :check :retained-version}
               (rejection #(ia/prepare root src))))
        ;; Generic source is meaningful; one iteration returns the retained
        ;; old value in the wrapper (or the other branch's constant vector).
        (is (vector? (call root src [1])))))))

(deftest helper-dependencies-and-old-worlds-coexist
  (let [wo (w/make-world) cache (stage/make-cache)]
    (d/define! wo (list 'def 'step step))
    (let [old (w/snapshot wo) src (source old kernel)
          candidate (ia/prepare old src)
          observe (fn [root cached? n]
                    (let [reads (atom #{})]
                      [(binding [w/*reads* reads]
                         (if cached? (stage/with-cache cache (call root src [n]))
                             (call root src [n]))) @reads]))]
      (is (= :installed (:status (staged/install! cache old candidate))))
      (is (= (observe old false 4) (observe old true 4)))
      ;; Change representation of the body without changing its behavior.
      (d/define! wo '(def step (fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))))
      (let [new (w/snapshot wo)]
        (is (= {:status :declined :reason :stale-world} (staged/install! cache new candidate)))
        (is (= (observe new false 4) (observe new true 4)))
        (is (= :installed (:status (staged/install! cache new (ia/prepare new src)))))
        (is (= 2 (count (stage/executables cache))))
        (doseq [root [old new old new] n [0 1 8]]
          (is (= (observe root false n) (observe root true n)))))
      (d/define! wo (list 'def 'step wrapped))
      (let [retaining (w/snapshot wo)]
        (is (= :retained-version (:check (rejection #(ia/prepare retaining src)))))
        (is (= (observe retaining false 1) (observe retaining true 1)))
        (is (= [4] (first (observe old true 4))))))))

(deftest summaries-cannot-hide-late-reads-or-effects
  (let [wo (w/make-world)]
    (d/define! wo (list 'def 'step step))
    (let [root (w/snapshot wo)
          late (source root '(fn [n] (let [s step]
                                      (loop [i 0 acc [0]]
                                        (if (< i n)
                                          (let [again step] (recur (inc i) (again acc))) acc)))))]
      (is (= :late-world-read (:check (rejection #(ia/prepare root late))))))
    (d/define! wo '(def step (fn [a] (do (perform :time/now) a))))
    (let [root (w/snapshot wo)]
      (is (= :helper-effect (:check (rejection #(ia/prepare root (source root kernel)))))))))

(deftest summaries-and-guards-are-rechecked
  (let [wo (w/make-world) cache (stage/make-cache)]
    (d/define! wo (list 'def 'step step))
    (let [root (w/snapshot wo) src (source root kernel)]
      (staged/install! cache root (ia/prepare root src))
      (let [exe (first (stage/executables cache))
            sid (first (keys (get-in exe [:inference :analysis :summaries])))]
        (is (nil? (stage/check-certificate exe)))
        (is (= :invalid-inferred-affine
               (stage/check-certificate
                 (assoc-in exe [:inference :analysis :summaries sid :retained-arguments] #{0}))))
        (is (= :assumption-mismatch
               (stage/check-certificate (update exe :guards
                                                #(set (remove (fn [g] (= :world (first g))) %))))))))))

(deftest private-reference-store-settles-on-exception
  (doseq [form
          ['(fn [n] (loop [i 0 acc [9223372036854775807]]
                      (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
           '(fn [n] (loop [acc [0] i 9223372036854775807]
                      (if (= n 1) (recur (assoc acc 0 (inc (nth acc 0))) (inc i)) acc)))]]
    (let [src (source w/empty-root form) inferred (ia/infer (term src))
          outside (a/new-store) private (a/new-store) before @outside]
      (is (= (base/observe #(call w/empty-root src [1]))
             (binding [a/*store* outside]
               (with-redefs [a/new-store (fn [] private)]
                 (base/observe #(ia/execute-owned inferred [1]))))))
      (is (= before @outside))
      (is (seq (:tokens @private)))
      (is (every? #(and (= :settled (:status %)) (nil? (get-in % [:payload :cell])))
                  (vals (:tokens @private)))))))
