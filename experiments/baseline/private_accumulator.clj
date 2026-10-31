(ns baseline.private-accumulator
  "Warm diagnostic of checked inline -> enclosed private accumulator composition."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.funding :as funding] [klara.compile.local-calls :as local]
            [klara.compile.staged :as staged] [klara.compile.subject :as subject]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as world]))

(def source
  '(fn [n bias limit]
     (let [step (fn [acc i]
                  (assoc (assoc acc 0 (+ (nth acc 0) i))
                         1 (+ (nth acc 1) bias)))]
       (let [acc (loop [i 0 acc [0 0]]
                   (if (< i n) (recur (inc i) (step acc i)) acc))]
         (< (+ (nth acc 0) (nth acc 1)) limit)))))

(def policy-source
  '(fn [r] (if (= (count (get r :history)) 0)
             {:action :local-call :planner 'klara.compiler/local-calls}
             {:action :private-accumulator})))

(defn- elapsed [f]
  (let [start (System/nanoTime) value (f)] {:value value :ns (- (System/nanoTime) start)}))
(defn- median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn run-study! [label]
  (let [w (world/make-world) _ (local/bootstrap! w)
        _ (defs/define! w (list 'def 'policy policy-source))
        _ (defs/define! w (list 'def 'f source)) root (world/snapshot w)
        code (defs/eval-form root (list 'code source)) s (subject/closed root code)
        variants {:baseline {:local-call-planner local/planner-symbol}
                  :private {:strategy 'policy}}
        prepared (into {} (for [[k opts] variants]
                            (let [job (funding/create {})
                                  r (elapsed #(staged/request root s (assoc opts :job job)))
                                  _ (assert (= :prepared (get-in r [:value :status])))
                                  p (get-in r [:value :candidate]) cache (stage/make-cache)
                                  installation (elapsed #(staged/install! cache root (staged/prevalidate p)))]
                              [k {:cache cache :info (staged/prepared-info p) :usage (funding/usage job)
                                  :preparation-ns (:ns r) :validation-installation-ns (:ns installation)}])))
        f (defs/lookup root 'f) args [10000 4 60000000]
        engines [:reference :baseline :private]
        call (fn [k]
               (binding [ev/*basis* root ev/*mint* root]
                 (stage/with-cache (or (get-in prepared [k :cache]) (stage/make-cache))
                   (ev/call-value f args))))
        _ (dotimes [_ 20] (doseq [k engines] (assert (true? (call k)))))
        samples (mapv (fn [i]
                        (into {} (for [k (take 3 (drop (mod i 3) (cycle engines)))]
                                   [k (:ns (elapsed #(assert (true? (call k)))))]))) (range 9))
        report {:source source :policy-source policy-source :arguments args :samples samples
                :median-ns (into {} (for [k engines] [k (median (map k samples))]))
                :java (System/getProperty "java.runtime.version")
                :preparation (into {} (for [[k p] prepared]
                                        [k (assoc (select-keys p [:usage :preparation-ns :validation-installation-ns])
                                                  :info (select-keys (:info p) [:code-id :rewrite-receipts :rewrite-summary
                                                                               :strategy-history :private-region]))]))
                :stats (into {} (for [[k p] prepared] [k (stage/stats (:cache p))]))
                :limits [:one-warm-process :one-input :trusted-tested-semantic-bridges
                         :final-freeze-still-allocates :no-performance-assertion :not-publication-evaluation]
                :source-sha256 (into {} (for [path (concat ["experiments/baseline/private_accumulator.clj"
                                                          "test/klara/compile/private_accumulator_test.clj"
                                                          "examples/compat/klara/private_optimizer.cljc"]
                                                         (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                         [path (core/sha256 (slurp path))]))}
        path (str "target/private-accumulator/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:median-ns :stats])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
