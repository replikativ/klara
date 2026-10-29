(require '[clojure.test.check.generators :as gen]
         '[klara.compile.generated-test :as generated]
         '[klara.compile.core-test :as core-test]
         '[klara.compile.core :as cc] '[klara.stage :as s])
(let [out (first *command-line-args*)
      cases (vec
             (for [[family generator count offset] [[:accepted generated/accepted-program 1000 90210]
                                                    [:hof generated/hof-program 250 15027]
                                                    [:rejected generated/rejected-program 250 901]]
                   i (range count)]
               (let [seed (+ offset (* i 100003)) p (gen/generate generator 20 seed)
                     result
                     (if (= family :rejected)
                       (let [wo (core-test/setup p) cache (s/make-cache)
                             rejected (try (cc/compile-def wo 'f) false
                                           (catch clojure.lang.ExceptionInfo e
                                             (= :compile (:klara/error (ex-data e)))))
                             trace (atom []) probes (generated/probes trace)]
                         (and rejected
                              (every? (fn [n]
                                        (let [call (list 'f n (list 'quote probes))
                                              form (if (= 'fn (first (nth p 2))) (list call) call)]
                                          (= (generated/observations wo form (s/make-cache) trace)
                                             (generated/observations wo form cache trace)))) [-1 0 2])))
                       (generated/equivalent? p))]
                 (when-not result (throw (ex-info "differential mismatch" {:family family :seed seed :program p})))
                 {:family family :seed seed :program p :agree result
                  :inputs (if (= family :rejected) 3 6)
                  :post-clear-comparisons (if (= family :rejected) 0 1)})))
      summary {:generated-programs (count cases) :distinct-syntax (count (set (map :program cases)))
               :families (frequencies (map :family cases)) :input-cases (reduce + (map :inputs cases))
               :post-clear-cases (reduce + (map :post-clear-comparisons cases))
               :disagreements 0 :classification {}}]
  (spit (str out "/generated.edn") (pr-str {:summary summary :cases cases}))
  (prn summary))
(shutdown-agents)
