(ns klara.compile.strategy-test
  (:require [clojure.test :refer [deftest is]] [klara.compile.staged :as staged]
            [klara.compile.subject :as subject] [klara.compile.edge :as edge]
            [klara.compile.funding :as funding] [klara.compile.local-calls :as local]
            [klara.compile.core :as compiler] [klara.compile.prepare :as prepare]
            [klara.compile.compose-driver-test :refer [nested-source]]
            [klara.compile.core-test :refer [observe]] [klara.defs :as defs]
            [klara.world :as world] [klara.stage :as stage] [klara.repl :as repl]))

(def strategy-source
  '(fn [r] (if (= 0 (count (get r :history))) {:action :inspect}
             (if (> (get (get r :source) :local-functions) 0)
               {:action :local-call :planner 'klara.compiler/local-calls}
               {:action :finish}))))

(defn setup []
  (let [w (world/make-world)]
    (local/bootstrap! w)
    (defs/define! w (list 'def 'strategy strategy-source))
    (defs/define! w (list 'def 'f nested-source)) w))

(deftest explicit-strategy-inspects-rewrites-and-finishes
  (let [w (setup) root (world/snapshot w)
        source (defs/eval-form root (list 'code nested-source))
        s (subject/closed root source) job (funding/create {})
        r (staged/request root s {:job job :strategy 'strategy :strategy-steps 4})
        p (:candidate r) info (staged/prepared-info p) cache (stage/make-cache)]
    (is (= :prepared (:status r)))
    (is (= [:inspect :local-call :local-call :finish] (mapv :action (:strategy-history info))))
    (is (= {:rounds 4 :stop :finished :calls-inlined 2} (:rewrite-summary info)))
    (is (= 2 (get-in info [:subject :evidence :checked-recipe-count])))
    (is (false? (get-in info [:subject :evidence :complete-semantic-proof?])))
    (is (false? (get-in info [:subject :memory :replayability-established?])))
    (is (= :experimental-projection (get-in info [:subject :contract :status])))
    (is (= :installed (:status (staged/install! cache root p))))
    (is (= [:value 35 ""] (observe w '(f 5) cache)))
    (is (pos? (:work (funding/usage job))))
    (is (= :declined (:status (staged/request root s {:job job :required-contract :host-contextual}))))
    (is (= :declined (:status (staged/request root s {:job job :backend :scalar}))))))

(deftest reference-world-and-policy-world-are-distinct
  (let [w (world/make-world)
        _ (defs/define! w '(def g (fn [x] (+ x 1))))
        _ (defs/define! w '(def f (fn [x] (g x))))
        root (world/snapshot w) code (defs/eval-form root '(code (fn [x] (g x))))
        s (subject/closed root code) policy (world/fork w)
        _ (local/bootstrap! policy)
        _ (defs/define! policy '(def strategy (fn [r] {:action :finish})))
        _ (defs/define! policy '(def g (fn [x] (+ x 100))))
        p (get (staged/request (world/snapshot policy) s
                 {:job (funding/create {}) :strategy 'strategy}) :candidate)
        cache (stage/make-cache)]
    (is (nil? (world/entry* root 'strategy)))
    (is (= :declined (:status (staged/install! cache (world/snapshot policy) p))))
    (is (= :installed (:status (staged/install! cache root p))))
    (is (= [:value 4 ""] (observe w '(f 3) cache)))))

(deftest opaque-edges-and-contracts-are-not-guest-assertions
  (let [w (setup) exe (compiler/compile-def w 'f {:mode :baseline :strategy 'strategy})
        accepted (first (:checked-edges exe))
        fake (klara.compile.edge.CheckedEdge. nil nil (edge/info accepted) (Object.))]
    (is (edge/checked? accepted))
    (is (false? (edge/checked? (edge/info accepted))))
    (is (false? (edge/checked? fake)))
    (is (some? (stage/check-certificate (assoc exe :checked-edges []))))
    (is (some? (stage/check-certificate (dissoc exe :rewrite-origin-id))))))

(deftest strategy-and-funding-rejections-do-not-publish
  (doseq [source ['(fn [r] {:action :finish :contract :weaker})
                  '(fn [r] {:action :unchecked :code 0})
                  '(fn [r] (clojure.core/atom 0))]]
    (let [w (setup) _ (defs/define! w (list 'def 'strategy source))
          code (defs/eval-form (world/snapshot w) (list 'code nested-source))
          r (staged/request (world/snapshot w) code
                            {:job (funding/create {}) :backend :baseline :strategy 'strategy})]
      (is (= :rejected (:status r)))
      (is (nil? (:candidate r)))))
  (let [w (setup) root (world/snapshot w) code (defs/eval-form root (list 'code nested-source))
        job (funding/create {:work 100})]
    (is (= :exhausted (:status (staged/request root code {:job job :backend :baseline :strategy 'strategy}))))
    (is (= :exhausted (:status (staged/request root code {:job job :backend :baseline :strategy 'strategy}))))
    (is (pos? (:work (funding/usage job))))))

(deftest runtime-staged-strategy-runs-in-a-real-fork
  (let [s (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response s
            (str "(require '[klara.strategy]) (def job (perform :stage/job {})) "
                 "(def code (code " (pr-str nested-source) ")) "
                 "(def kernel (run code)) (def subject (klara.strategy/subject code)) "
                 "(klara.strategy/prepare job subject) (kernel 5)"))]
    (is (empty? (:errors r)))
    (is (.endsWith ^String (:output r) "35"))
    (is (= 1 (count (stage/executables (:cache s)))))
    (is (pos? (:hits (stage/stats (:cache s)))))
    (let [changed (repl/eval-response s
                    "(def klara.strategy/strategy (fn [r] {:action :finish})) (klara.strategy/prepare job subject) (kernel 5)")]
      (is (empty? (:errors changed)))
      (is (.contains ^String (:output changed) ":status :declined"))
      (is (.endsWith ^String (:output changed) "35"))
      (is (= 1 (count (stage/executables (:cache s))))))))
