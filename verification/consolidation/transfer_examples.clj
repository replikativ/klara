(ns consolidation.transfer-examples
  "Executable transfer examples and proof instrumentation for one compiler job.
   The with-redefs observer is a diagnostic harness, not an operational policy."
  (:require [klara.compile.loop :as loop] [klara.compile.staged :as staged]
            [klara.code :as code] [klara.defs :as d] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as w]
            [consolidation.transfer :as transfer]))

(def examples
  [{:name :swap
    :form '(fn [n] (loop [i 0 a 1 b 2]
                     (if (< i n) (recur (inc i) b a) (+ (* 10 a) b))))
    :inputs [[0] [1] [2] [7]] :expected [12 21 12 21]}
   {:name :recurrence
    :form '(fn [n] (loop [i 0 a 1 b 2]
                     (if (< i n) (recur (inc i) b (+ a b)) a)))
    :inputs [[0] [1] [5] [12]] :expected [1 2 13 377]}
   {:name :euclid
    :form '(fn [x y] (loop [a x b y]
                       (if (> a b) (recur (- a b) b)
                         (if (< a b) (recur a (- b a)) a))))
    ;; Positive inputs: no fixed stride or statically known iteration count.
    :inputs [[48 18] [21 14] [17 17]] :expected [6 7 17]}])

(defn prepare-with-evidence [source]
  (let [checks (atom []) check loop/check-transfer!
        candidate (with-redefs [loop/check-transfer!
                                (fn [destinations arguments plan]
                                  (let [shape (check destinations arguments plan)]
                                    (swap! checks conj {:destinations destinations :arguments arguments :plan plan})
                                    shape))]
                    (staged/prepare w/empty-root source))
        transfers (mapv (fn [{:keys [destinations arguments plan] :as entry}]
                          (assoc entry :receipt (transfer/certify destinations arguments plan))) @checks)]
    {:candidate candidate :transfers transfers}))

(defn run-example [{:keys [name form inputs expected]}]
  (let [source (d/eval-form w/empty-root (list 'code form))
        core (code/s->core (code/code-term source)) closure (ev/run core)
        {:keys [candidate transfers]} (prepare-with-evidence source)
        cache (stage/make-cache)
        _ (staged/install! cache w/empty-root candidate)
        values (mapv #(stage/with-cache cache (ev/call-value closure %)) inputs)]
    (assert (= expected values (mapv #(ev/call-value closure %) inputs)))
    (assert (= (count inputs) (:hits (stage/stats cache))))
    (assert (every? (fn [{:keys [destinations arguments plan receipt]}]
                      (transfer/verify? destinations arguments plan receipt)) transfers))
    {:example name :values values :stage-stats (stage/stats cache)
     :transfer-evidence (mapv (fn [{:keys [receipt]}]
                                (select-keys receipt [:shape :checker-version :model-id :goal-sha256 :proof-sha256])) transfers)}))

(defn -main [& _]
  (doseq [example examples] (prn (run-example example))))
