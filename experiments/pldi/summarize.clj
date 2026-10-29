(require '[clojure.edn :as edn] '[clojure.java.io :as io] '[clojure.pprint])
(let [dir (first *command-line-args*)
      generated (edn/read-string (slurp (str dir "/generated.edn")))
      spec (edn/read-string (slurp (str dir "/spec.edn")))
      files (sort-by str (filter #(re-matches #"run-.*\.edn" (.getName %)) (.listFiles (io/file dir))))
      runs (mapv #(edn/read-string (slurp %)) files)
      forced (for [run runs :when (= :compiled (:mode run))
                   [family record] (get-in run [:details :forced])]
               {:family family :checkpoints (count (:frame-states record))
                :forced-exits (reduce + (map :deopts (:comparisons record)))})
      info {:generated (:summary generated)
            :spec (select-keys spec [:programs :agreements :disagreements])
            :spec-classification (into {} (for [c (:cases spec) :when (not (:agree c))] [(:name c) (:known c)]))
            :forced {:families (frequencies (map :family forced))
                     :checkpoints (reduce + (map :checkpoints forced))
                     :exits (reduce + (map :forced-exits forced)) :disagreements 0}
            :naive-deopt (get-in (first (filter #(= :compiled (:mode %)) runs)) [:details :naive-deopt])
            :smc (mapv #(get-in % [:details :smc]) runs)}]
  (spit (str dir "/rq5.tex")
        (str "\\begin{tabular}{lr}\n\\toprule Case & Count \\\\ \n\\midrule\n"
             "Generated programs & " (get-in info [:generated :generated-programs]) " \\\\ \n"
             "Distinct syntax & " (get-in info [:generated :distinct-syntax]) " \\\\ \n"
             "Input cases & " (get-in info [:generated :input-cases]) " \\\\ \n"
             "Compiler disagreements & " (get-in info [:generated :disagreements]) " \\\\ \n"
             "Forced exits & " (get-in info [:forced :exits]) " \\\\ \n"
             "Spec cases & " (:programs spec) " \\\\ \n"
             "Classified spec differences & " (:disagreements spec) " \\\\ \n"
             "\\bottomrule\n\\end{tabular}\n"))
  (spit (str dir "/correctness.csv")
        (str "metric,count\n"
             "Generated programs," (get-in info [:generated :generated-programs]) "\n"
             "Distinct syntax," (get-in info [:generated :distinct-syntax]) "\n"
             "Input cases," (get-in info [:generated :input-cases]) "\n"
             "Cache deletion cases," (get-in info [:generated :post-clear-cases]) "\n"
             "Compiler disagreements," (get-in info [:generated :disagreements]) "\n"
             "Forced exits," (get-in info [:forced :exits]) "\n"
             "Spec cases," (:programs spec) "\n"
             "Spec agreements," (:agreements spec) "\n"
             "Classified spec differences," (:disagreements spec) "\n"))
  (spit (str dir "/mixed-types.csv")
        (str "process,nonlong_per_1000,calls,deopts,hits,fallbacks\n"
             (apply str (map-indexed
                         (fn [i run]
                           (when (= :compiled (:mode run))
                             (apply str (for [[rate r] (get-in run [:details :mixed])]
                                          (str i "," rate "," (:calls r) "," (get-in r [:stats :deopts]) ","
                                               (get-in r [:stats :hits]) "," (get-in r [:stats :fallbacks]) "\n"))))) runs))))
  (spit (str dir "/correctness.edn") (pr-str info))
  (spit (str dir "/correctness.txt") (with-out-str (clojure.pprint/pprint (dissoc info :smc))))
  (spit (str dir "/events.csv")
        (str "process,kind,size,ns\n"
             (apply str
                    (map-indexed
                     (fn [i run]
                       (when (= :compiled (:mode run))
                         (str (apply str (for [[n r] (get-in run [:details :redefinition])
                                               e (:events r) kind [:publish-ns :first-correct-ns :total-ns]]
                                           (str i "," (name kind) "," n "," (kind e) "\n")))
                              (apply str (for [t (get-in run [:details :recovery-ns])]
                                           (str i ",recovery,1," t "\n")))))) runs)))))
(shutdown-agents)
