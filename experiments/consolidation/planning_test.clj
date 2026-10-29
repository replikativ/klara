(ns consolidation.planning-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.planning :as planner] [proof-staging :as ps]
            [klara.authority :as authority] [klara.world :as w] [klara.defs :as d]
            [klara.eval :as ev] [klara.core :as c] [klara.stage :as stage]
            [klara.compile.staged :as staged]))

(def limits {:search-fuel 16 :transition-fuel 100000})
(defn fixture [] (planner/problem [1 2 3] {:max-count 64 :max-x 10}))
(defn choose [root policy problem calls]
  (planner/invoke-policy root policy [problem {:remaining-calls calls} (assoc limits :preparation-ns 1000000000)]
                         (:transition-fuel limits)))

(deftest guest-search-selects-distinct-paths-and-stop
  (let [root (w/snapshot (planner/load-world)) problem (fixture)
        both (choose root 'plan-optimizer problem 10000)
        only-fusion (choose root 'plan-optimizer (assoc-in problem [:estimates :run-ns :both] 50000) 10000)
        stop (choose root 'plan-optimizer problem 0)]
    (is (= :completed (:status both)))
    (is (= :both (get-in both [:value :node])))
    (is (= [:numeric :fusion] (mapv :kind (get-in both [:value :steps]))))
    (is (= :stream (get-in only-fusion [:value :node])))
    (is (= [:fusion] (mapv :kind (get-in only-fusion [:value :steps]))))
    (is (= :stop (get-in stop [:value :action])))
    (is (= 5 (get-in both [:value :expanded])))
    (is (pos? (:transitions both)))
    (let [bounded (planner/invoke-policy root 'plan-optimizer
                    [problem {:remaining-calls 10000} {:search-fuel 1 :preparation-ns 1000000000}] 100000)]
      (is (= :stop (get-in bounded [:value :action])))
      (is (true? (get-in bounded [:value :search-exhausted]))))))

(deftest actual-transition-fuel-and-effect-boundary
  (let [world (planner/load-world) problem (fixture)]
    (d/define! world '(def forever (fn [p profile limits] (loop [] (recur)))))
    (is (= {:status :pending :reason :transition-budget :transitions 200}
           (select-keys (planner/invoke-policy (w/snapshot world) 'forever [problem {} {}] 200)
                        [:status :reason :transitions])))
    (doseq [form ['(def bad (fn [p profile limits] (perform :stage/install p)))
                  '(def bad (fn [p profile limits] (clojure.core/spit "/tmp/klara-forbidden-policy" "bad")))
                  '(def bad (let [x 1] (fn [p profile limits] x)))]]
      (d/define! world form)
      (is (thrown? clojure.lang.ExceptionInfo (choose (w/snapshot world) 'bad problem 10000))))
    (is (thrown? clojure.lang.ExceptionInfo
          (planner/invoke-policy (w/snapshot world) 'plan-optimizer [(assoc problem :foreign inc) {} {}] 100)))
    (with-redefs [c/prims (assoc c/prims '+ -)]
      (is (thrown? clojure.lang.ExceptionInfo (choose (w/snapshot world) 'plan-optimizer problem 10000))))))

(deftest fixed-validator-binds-the-reference-and-rejects-invalid-proposals
  (let [root (w/snapshot (planner/load-world)) problem (fixture)
        plan (:value (choose root 'plan-optimizer problem 10000))
        prepared (planner/prepare-plan w/empty-root problem plan) cache (stage/make-cache)]
    (is (= :prepared (:status prepared)))
    (is (true? (:fork-exited prepared)))
    (is (= :authority-fork (:preparation-isolation prepared)))
    (is (= :installed (:status (staged/install! cache w/empty-root (:candidate prepared)))))
    (is (= 57 (stage/with-cache cache (ps/run-code (get-in problem [:codes :source]) [1 2 3]))))
    (is (pos? (:hits (stage/stats cache))))
    (doseq [bad [(assoc-in plan [:steps 0 :coefficients] [1 2 4])
                 (assoc plan :source (get-in problem [:codes :both]))
                 (assoc-in plan [:domain :max-x] 11)
                 (assoc-in plan [:domain :max-x] 10N)]]
      (let [result (planner/prepare-plan w/empty-root problem bad)]
        (is (= :declined (:status result)))
        (is (pos? (:elapsed-ns result)))))
    (doseq [xs [[11] [-1] [1N] '(1 2)]]
      (is (= (ps/run-code (get-in problem [:codes :source]) xs)
             (stage/with-cache cache (ps/run-code (get-in problem [:codes :source]) xs)))))))

(deftest controller-charges-total-work-and-avoids-identical-attempts
  (let [world (planner/load-world) root (w/snapshot world) problem (fixture) cache (stage/make-cache)
        initial (planner/controller 10000000000 3)
        run #(planner/invest cache w/empty-root root 'plan-optimizer problem {:remaining-calls 10000} limits %)
        first-result (run initial) second-result (run (:controller first-result))
        entry (first (get-in first-result [:controller :history]))]
    (is (= :installed (:status first-result)))
    (is (= :already-attempted (:reason second-result)))
    (is (= 2 (get-in second-result [:controller :remaining-attempts])))
    (is (= (:total-ns entry) (- (:remaining-ns initial) (get-in first-result [:controller :remaining-ns]))))
    (is (>= (:total-ns entry) (+ (:planning-ns entry) (:preparation-ns entry) (:publication-ns entry))))
    (is (= :stopped (:status (run (planner/controller 0 1)))))))

(deftest failed-proof-work-is-charged-without-publication
  (let [world (planner/load-world) problem (fixture) cache (stage/make-cache)]
    (d/define! world
      '(def wrong-policy
         (fn [p profile limits]
           (let [plan (plan-optimizer p profile limits)]
             (assoc plan :steps [{:kind :numeric :coefficients [1 2 4]} {:kind :fusion}])))))
    (let [result (planner/invest cache w/empty-root (w/snapshot world) 'wrong-policy problem
                                {:remaining-calls 10000} limits (planner/controller 10000000000 2))
          entry (first (get-in result [:controller :history]))]
      (is (= :declined (:status result)))
      (is (pos? (:preparation-ns entry)))
      (is (pos? (:total-ns entry)))
      (is (= 1 (get-in result [:controller :remaining-attempts])))
      (is (empty? (stage/executables cache))))))

(deftest a-guest-optimizer-evolves-in-a-world-while-the-validator-stays-fixed
  (let [manager (planner/load-world) fiber (w/fiber manager) store (authority/new-store)
        evaluate (fn [form]
                   (w/raise-basis! fiber)
                   (binding [authority/*store* store ev/*fiber* fiber]
                     (if (and (seq? form) (= 'def (first form))) (d/define! manager form) (d/eval-in fiber form))))
        problem (fixture) cache (stage/make-cache) registry @stage/checkers]
    (evaluate '(def optimizer (fn [p profile limits] (conservative-optimizer p profile limits))))
    (evaluate '(def compiler-world (perform :world/fork)))
    (let [compiler (d/lookup (w/snapshot manager) 'compiler-world) old-root (w/snapshot compiler)]
      (evaluate '(def job (branch! {:compiler compiler-world})))
      (evaluate '(perform :world/eval-in (system job :compiler)
                          '(def optimizer (fn [p profile limits] (plan-optimizer p profile limits)))))
      (let [branch (evaluate '(system job :compiler)) branch-root (w/snapshot branch)
            plan (:value (choose branch-root 'optimizer problem 500))
            prepared (planner/prepare-plan w/empty-root problem plan)]
        (is (= :stop (get-in (choose old-root 'optimizer problem 500) [:value :action])))
        (is (= :both (:node plan)))
        (is (= :prepared (:status prepared)))
        (is (empty? (stage/executables cache)))
        (is (= {:merged [:compiler]} (evaluate '(merge! job))))
        (is (= :installed (:status (staged/install! cache w/empty-root (:candidate prepared)))))
        (is (= :both (get-in (choose (w/snapshot compiler) 'optimizer problem 500) [:value :node])))
        (is (= :stop (get-in (choose old-root 'optimizer problem 500) [:value :action])))
        (is (identical? registry @stage/checkers))
        (is (= 57 (stage/with-cache cache (ps/run-code (get-in problem [:codes :source]) [1 2 3]))))))))
