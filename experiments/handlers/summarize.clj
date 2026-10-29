;; clojure -M summarize.clj results/raw-openjdk25-c2.edn
;; Prints a markdown table: per benchmark, the minimum over rounds of the
;; per-JVM best sample, the median over rounds of the per-JVM median sample,
;; the spread of per-JVM medians, and the slowdown vs its baseline (best/best).
(require '[clojure.edn :as edn] '[clojure.string :as str])

(def baseline
  {"i" :i/direct-fn "iii" nil "abort" :abort/ret-d10 "ii" nil})

(defn base-of [id]
  (case (namespace id)
    "i" :i/direct-fn
    "abort" :abort/ret-d10
    "iii" (if (#{:iii/none-1e7 :iii/fast-outer :iii/maybe-fast :iii/maybe-cps} id)
            :iii/none-1e7 :iii/none-iter)
    "ii" (cond (str/includes? (name id) "enum") :ii/enum-direct
               :else :ii/is-direct)))

(defn median [xs] (let [v (vec (sort xs))] (nth v (quot (count v) 2))))

(let [f (first *command-line-args*)
      runs (->> (str/split-lines (slurp f))
                (remove str/blank?)
                (map edn/read-string)
                (map :run))
      by (group-by :id runs)
      stat (into {} (for [[id rs] by]
                      [id {:best (apply min (map :min rs))
                           :med (median (map :median rs))
                           :lo (apply min (map :median rs))
                           :hi (apply max (map :median rs))
                           :n (count rs)
                           :result (:result (first rs))}]))
      order ["i" "iii" "abort" "ii"]]
  (println "JVM:" (:vm (first runs)) (:java (first runs)) " file:" f)
  (println)
  (println "| benchmark | unit | best ns | median ns | median range | best / baseline | baseline |")
  (println "|---|---|---:|---:|---|---:|---|")
  (doseq [g order
          id (sort (filter #(= g (namespace %)) (keys stat)))]
    (let [{:keys [best med lo hi n]} (stat id)
          b (base-of id)
          bb (:best (stat b))
          unit (case g "i" "perform" "iii" "iteration" "abort" "iteration"
                     "ii" (if (str/includes? (name id) "enum") "path" "particle"))]
      (println (format "| %s | %s | %.2f | %.2f | %.2f–%.2f (n=%d) | %s | %s |"
                       id unit best med lo hi n
                       (if bb (format "%.2fx" (/ best bb)) "")
                       (or b ""))))))
