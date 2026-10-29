(require '[klara.spec-diff-test :as diff] '[clojure.test :as t])
(let [rs (diff/compare-all)
      summary (with-redefs [diff/compare-all (constantly rs)] (t/run-tests 'klara.spec-diff-test))]
  (spit (str (first *command-line-args*) "/spec.edn")
        (pr-str {:summary summary :programs (count rs) :agreements (count (filter :agree rs))
                 :disagreements (count (remove :agree rs)) :cases rs}))
  (assert (zero? (+ (:fail summary) (:error summary)))))
(shutdown-agents)
