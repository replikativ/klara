(ns klara.staged-compile-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [klara.authority :as a]
            [klara.code :as code]
            [klara.compile.staged :as sc]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn example-world []
  (let [wo (w/make-world)]
    (with-open [r (java.io.PushbackReader. (io/reader "examples/staging/07-staged-regions.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
        (d/define! wo form))) wo))

(defn closure [source root]
  (ev/run (code/s->core (code/code-term source)) {:basis root}))
(defn call [cache root source args]
  (stage/with-cache cache (ev/call-value (closure source root) args)))
(defn observe [f]
  (try [:value (f)] (catch Throwable e [:exception (class e)])))

(deftest staged-program-and-bounded-policy
  (let [wo (example-world) root (w/snapshot wo) cache (stage/make-cache)
        store (a/new-store) inputs [10 12 14 16 10.5 8 5]
        expected (mapv #(d/eval-form root (list 'kernel %)) inputs)
        result (binding [a/*store* store]
                 (stage/with-cache cache
                   (d/eval-form root (list 'operate 'kernel-code inputs 2))))]
    (is (= expected (:values result)))
    (is (= 2 (:long-count result)))
    (is (= :installed (get-in result [:publication :status])))
    (is (= 1 (count (stage/executables cache))))
    (is (pos? (:hits (stage/stats cache))))
    (is (pos? (:fallbacks (stage/stats cache))))
    ;; The child used the actual owned store; its scratch cannot remain live.
    (is (seq (:tokens @store)))
    (is (every? #(= :settled (:status %)) (vals (:tokens @store))))
    (stage/clear! cache)
    (is (= expected (stage/with-cache cache
                      (mapv #(d/eval-form root (list 'kernel %)) inputs)))))
  (let [wo (example-world) root (w/snapshot wo) cache (stage/make-cache)]
    ;; The same lifecycle operation can run before any operational sample.
    (is (= :installed (:status (binding [a/*store* (a/new-store)]
                                (stage/with-cache cache (d/eval-form root '(refine kernel-code)))))))
    (is (= 7993 (stage/with-cache cache (d/eval-form root '(kernel 10)))))))

(deftest typed-region-differential
  (doseq [[form cases]
          [['(fn [n] (+ n 1)) [[0] [9] [Long/MAX_VALUE] [1.5] [1/2] [1N]]]
           ['(fn [a b] (- a b)) [[0 1] [Long/MIN_VALUE 1] [4.5 2]]]
           ['(fn [a b] (* a b)) [[3 7] [Long/MAX_VALUE 2] [1/2 4]]]
           ['(fn [a] (dec a)) [[0] [Long/MIN_VALUE]]]
           ['(fn [a b] (if (<= a b) (if (= a b) 3 4) 5)) [[1 2] [2 2] [3 2]]]
           ['(fn [n] (loop [i 0 a 1 b 2]
                       (if (< i n) (recur (inc i) b a) (+ (* 10 a) b))))
            [[0] [1] [2] [11] [10.5]]]
           ['(fn [n] (loop [i 0 total 0]
                       (if (< i n) (recur (inc i) (+ total (* i i))) total)))
            (mapv vector (range -2 25))]]]
    (let [source (d/eval-form w/empty-root (list 'code form))
          candidate (sc/prepare w/empty-root source) cache (stage/make-cache)]
      (is (= :installed (:status (sc/install! cache w/empty-root candidate))))
      (doseq [args cases]
        (is (= (observe #(ev/call-value (closure source w/empty-root) args))
               (observe #(call cache w/empty-root source args))) (pr-str [form args])))
      (stage/clear! cache)
      (doseq [args cases]
        (is (= (observe #(ev/call-value (closure source w/empty-root) args))
               (observe #(call cache w/empty-root source args))))))))

(deftest world-validity-and-current-recorder
  (let [wo (example-world) old (w/snapshot wo) source (d/lookup old 'kernel-code)
        cache (stage/make-cache) candidate (sc/prepare old source)
        read-call (fn [root cached?]
                    (let [reads (atom #{})]
                      [(binding [w/*reads* reads]
                         (if cached? (call cache root source [10])
                           (ev/call-value (closure source root) [10]))) @reads]))]
    (sc/install! cache old candidate)
    (is (= (read-call old false) (read-call old true)))
    (is (= (read-call old true) (read-call old true)))
    (d/define! wo '(def calibration 7))
    (let [new (w/snapshot wo)]
      (is (= :declined (:status (sc/install! cache new candidate))))
      (is (not= (first (read-call old true)) (first (read-call new true))))
      (is (= (read-call new false) (read-call new true)))
      (is (= :installed (:status (sc/install! cache new (sc/prepare new source)))))
      (is (= 2 (count (stage/executables cache))))
      (doseq [root [old new old new]]
        (is (= (read-call root false) (read-call root true)))))))

(deftest handlers-and-no-effect-replay
  (let [wo (w/make-world) cache (stage/make-cache)]
    (d/define! wo '(def c (code (fn [x] (inc x)))))
    (d/define! wo '(def f (run c)))
    (let [root (w/snapshot wo)]
      (sc/install! cache root (sc/prepare root (d/lookup root 'c)))
      (is (= :caught (stage/with-cache cache
                        (d/eval-form root '(handle :dynamic {:exn/raise (fn [e k] :caught)}
                                            (f 9223372036854775807))))))
      (is (= 0 (:hits (stage/stats cache))))
      (is (= 1 (:fallbacks (stage/stats cache))))
      (is (= :custom (d/eval-form root '(handle :dynamic {:stage/layout (fn [args k] (k :custom))}
                                         (perform :stage/layout [1])))))))
  (let [wo (w/make-world) log (atom [])]
    ;; prepare analyzes data, it cannot execute the rejected body or callback.
    (d/define! wo (list 'def 'log (list 'quote log)))
    (is (= :declined (:status (d/eval-form (w/snapshot wo)
                               '(perform :stage/prepare (code (fn [n] (swap! log conj n))))))))
    (is (= [] @log))))

(deftest unsupported-models-and-read-order
  (let [wo (example-world) root (w/snapshot wo)]
    (doseq [coefficients [[1.5 2] [1/2 1] [1N 2]]]
      (let [cache (stage/make-cache)
            source (d/eval-form root (list 'make-kernel coefficients))
            result (binding [a/*store* (a/new-store)]
                     (stage/with-cache cache
                       (d/eval-form root (list 'operate (list 'quote source) [3 4 5] 1))))]
        (is (= :declined (get-in result [:publication :status])))
        (is (= (mapv #(ev/call-value (closure source root) [%]) [3 4 5]) (:values result)))
        (is (empty? (stage/executables cache)))))
    ;; A conditional world read, or one following possibly failing arithmetic,
    ;; must not be eagerly recorded by this first region implementation.
    (doseq [form ['(fn [n] (if (< n 0) calibration n))
                 '(fn [n] (let [x (inc n) y calibration] (+ x y)))
                 '(fn [n] (quot n 2))]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (sc/prepare root (d/eval-form root (list 'code form))))))))

(deftest fork-publication-and-authority-boundary
  (let [wo (example-world) root (w/snapshot wo) cache (stage/make-cache)]
    (binding [a/*store* (a/new-store)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"install must follow fork exit"
            (stage/with-cache cache
              (d/eval-form root '(fork [job (perform :stage/install (perform :stage/prepare kernel-code))]
                                   (adopt! job)))))))
    (is (empty? (stage/executables cache))))
  (let [wo (example-world) root (w/snapshot wo)
        candidate (sc/prepare root (d/lookup root 'kernel-code))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot lift"
          (d/eval-form root (list 'lift (list 'quote candidate))))))
  (binding [a/*store* (a/new-store)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned"
          (d/eval-form w/empty-root '(let [operational (own 1)]
                                      (fork [job 7] (adopt! job))))))))

(deftest concurrent-prepare-atomic-install
  (let [wo (example-world) root (w/snapshot wo) source (d/lookup root 'kernel-code)
        cache (stage/make-cache) prepared (promise) release (promise)
        job (future (let [p (sc/prepare root source)]
                      (deliver prepared p)
                      @release
                      (sc/install! cache root p)))]
    (try
      (is (not= ::timeout (deref prepared 30000 ::timeout)))
      ;; The independent compiler job has completed all class loading, but
      ;; publication is blocked. Operational readers still run T0 successfully.
      (is (empty? (stage/executables cache)))
      (dotimes [_ 8] (is (= 7993 (call cache root source [10]))))
      (is (= 0 (:hits (stage/stats cache))))
      (deliver release true)
      (is (= :installed (:status (deref job 30000 {:status ::timeout}))))
      (is (= 1 (count (stage/executables cache))))
      (dotimes [_ 8] (is (= 7993 (call cache root source [10]))))
      (is (= 8 (:hits (stage/stats cache))))
      (finally (deliver release true) (future-cancel job)))))

(deftest redefine-during-isolated-preparation
  (let [wo (example-world) old (w/snapshot wo) source (d/lookup old 'kernel-code)
        cache (stage/make-cache) ready (promise) release (promise)
        job (future (let [p (sc/prepare old source)]
                      (deliver ready p)
                      @release
                      (sc/install! cache (w/snapshot wo) p)))]
    (try
      (let [p (deref ready 30000 ::timeout)]
        (is (not= ::timeout p))
        (d/define! wo '(def calibration 7))
        (let [new (w/snapshot wo)]
          (is (not= (call cache old source [10]) (call cache new source [10])))
          (deliver release true)
          (is (= {:status :declined :reason :stale-world} (deref job 30000 ::timeout)))
          (is (empty? (stage/executables cache)))
          ;; The same completed candidate can still serve the pinned old root.
          (is (= :installed (:status (sc/install! cache old p))))
          (is (= 7993 (call cache old source [10])))
          (is (= (ev/call-value (closure source new) [10]) (call cache new source [10])))))
      (finally (deliver release true) (future-cancel job)))))

(deftest re-evaluating-identical-source-cannot-reuse-a-different-value-generation
  (let [world (w/make-world) actual (atom 1)]
    (with-redefs [ev/reference-handlers (assoc ev/reference-handlers :stage/test-definition-value (fn [_ _] @actual))]
      (d/define! world '(def calibration (perform :stage/test-definition-value)))
      (let [old (w/snapshot world)
            source (d/eval-form old '(code (fn [x] (let [bias calibration] (+ bias x)))))
            candidate (sc/prepare old source) cache (stage/make-cache)]
        (sc/install! cache old candidate)
        (reset! actual 9)
        (d/define! world '(def calibration (perform :stage/test-definition-value)))
        (let [new (w/snapshot world)]
          (is (= (get-in old [:defs 'calibration :code-id]) (get-in new [:defs 'calibration :code-id])))
          (is (not= (get-in old [:defs 'calibration :value-id]) (get-in new [:defs 'calibration :value-id])))
          (is (= 10 (call cache new source [1])))
          (is (= 2 (call cache old source [1])))
          (is (= :declined (:status (sc/install! cache new candidate))))
          (is (= :installed (:status (sc/install! cache new (sc/prepare new source)))))
          (is (= 10 (call cache new source [1]))))))))
