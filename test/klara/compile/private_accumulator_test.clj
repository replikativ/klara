(ns klara.compile.private-accumulator-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.support :refer [source strategy setup]] [klara.code :as code]
            [klara.compile.budget :as budget] [klara.compile.funding :as funding]
            [klara.compile.local-calls :as local] [klara.compile.private-accumulator :as private]
            [klara.compile.staged :as staged] [klara.compile.subject :as subject]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.repl :as repl] [klara.stage :as stage] [klara.world :as world]))

(defn observation [root f args cache]
  (binding [ev/*basis* root ev/*mint* root]
    (try (let [value (stage/with-cache cache (ev/call-value f args))]
           [:value value (class value)])
         (catch Throwable e [:error (class e) (.getMessage e)]))))

(deftest inline-and-private-lowering-share-original-entry-and-funding
  (let [w (setup source) root (world/snapshot w)
        c (defs/eval-form root (list 'code source)) job (funding/create {})
        r (staged/request root (subject/closed root c) {:job job :strategy 'strategy})
        p (:candidate r) info (staged/prepared-info p)
        exe (.-executable ^klara.compile.staged.Prepared p)
        cache (stage/make-cache) f (defs/lookup root 'f)]
    (is (= :prepared (:status r)))
    (is (= (core/code-id (code/s->core (code/code-term c))) (:code-id info)))
    (is (= [:local-call :private-accumulator] (mapv :action (:strategy-history info))))
    (is (= [:local-call-inline-v1 :enclosed-private-accumulator-v1] (mapv :rule (:rewrite-receipts info))))
    (is (= :boolean (get-in info [:private-region :result])))
    (is (seq (get-in info [:private-region :representations])))
    (is (= 1 (:emissions (funding/usage job))))
    (is (true? (get-in info [:subject :memory :ownership-checked?])))
    (is (= :installed (:status (staged/install! cache root (staged/prevalidate p)))))
    (doseq [args [[0 1 0] [0 1 1] [-1 2 0] [1 2 3] [5 3 26] [100 4 1000]
                  [3 -2 4] [2 Long/MAX_VALUE 0] [1.5 2 4]]]
      (is (= (observation root f args (stage/make-cache)) (observation root f args cache))))
    (is (pos? (:hits (stage/stats cache))))
    (is (pos? (:fallbacks (stage/stats cache))))
    (is (some? (stage/check-certificate (assoc exe :checked-edges []))))
    (is (some? (stage/check-certificate (dissoc exe :private-endpoint))))
    (is (some? (stage/check-certificate (assoc exe :guards #{}))))))

(deftest private-boundary-rejections-do-not-publish
  (doseq [consumer ['acc '(= acc acc) '(nth acc 100) '(< (nth acc limit) 10)
                    '(clojure.core/identical? acc acc)]]
    (let [form (list 'fn '[n bias limit]
                    (list 'let ['acc '(loop [i 0 acc [0 0]]
                                       (if (< i n)
                                         (recur (inc i) (assoc acc 0 (+ (nth acc 0) bias))) acc))]
                          consumer))
          w (setup form) root (world/snapshot w) job (funding/create {})
          r (staged/request root (defs/eval-form root (list 'code form)) {:job job :strategy 'strategy})]
      (is (= :declined (:status r)))
      (is (nil? (:candidate r)))
      (is (zero? (get (funding/usage job) :emissions 0)))))
  (let [w (setup source) root (world/snapshot w)
        _ (defs/define! w '(def strategy (fn [r] {:action :private-accumulator})))
        r (staged/request (world/snapshot w) (subject/closed root (defs/eval-form root (list 'code source)))
                          {:job (funding/create {}) :strategy 'strategy})]
    (is (= :declined (:status r)))))

(deftest exhausted-owned-attempts-keep-their-spend
  (let [w (setup source) root (world/snapshot w) c (defs/eval-form root (list 'code source))
        job (funding/create {:emissions 0})]
    (is (= :exhausted (:status (staged/request root c {:job job :strategy 'strategy}))))
    (is (pos? (:work (funding/usage job))))
    (is (pos? (:bytes (funding/usage job))))
    (is (= :exhausted (:status (staged/request root c {:job job :strategy 'strategy}))))))

(deftest staged-guest-policy-prepares-in-a-fork
  (let [session (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response session
            (str "(require '[klara.private-optimizer]) "
                 "(def source (code " (pr-str source) ")) (def kernel (run source)) "
                 "(def subject (perform :stage/subject source)) "
                 "(def job (perform :stage/job {})) "
                 "(klara.private-optimizer/prepare job subject) (kernel 5 3 26)"))]
    (is (empty? (:errors r)))
    (is (.endsWith ^String (:output r) "true"))
    (is (= 1 (count (stage/executables (:cache session)))))
    (is (pos? (:hits (stage/stats (:cache session)))))))
