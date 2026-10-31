(ns klara.lifetime-test
  "Collectability obligations (design/01-lifetimes.md#obligations-and-tests).
  Each test holds a weak reference to something a lifetime rule says must
  become unreachable, drops the program's references, and checks that the
  garbage collector clears it."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k])
  (:import [java.lang.ref WeakReference]))

(defn collected?
  "Run the collector until `ref` clears, up to a bound."
  [^WeakReference ref]
  (loop [i 0]
    (cond (nil? (.get ref)) true
          (> i 30) false
          :else (do (System/gc) (Thread/sleep 20) (byte-array (* 1024 1024)) (recur (inc i))))))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(defn- weak [x] (WeakReference. x))

(deftest L1-retain-history
  (testing "L1.retain.history: redefining releases the previous world"
    (let [s (session)
          _ (k/eval-string s "(def x 1)")
          old (weak (:world @s))]
      (k/eval-string s "(def x 2) (def x 3)")
      (is (collected? old))
      (is (= 3 (k/eval-string s "x"))))))

(deftest L1-slice-footprint
  (testing "L1.slice.footprint: a pinned function retains its footprint, not its world"
    (let [s (session)
          _ (k/eval-string s "(ns m (:require [klara.world :as world]))
                              (def dataset (vec (range 200000)))
                              (def setting 7)
                              (defn reader [] setting)
                              (def pinned (world/get (world/current) 'm/reader))")
          old-data (weak (k/eval-string s "dataset"))]
      (k/eval-string s "(def dataset [])")
      (is (collected? old-data))
      (is (= 7 (k/eval-string s "(pinned)")))
      (is (= '#{m/reader m/setting} (k/eval-string s "(world/footprint pinned)"))))))

(deftest L3-job-discard
  (testing "L3.job.discard: dropping an outcome releases its world"
    (let [s (session)
          job-world (weak (k/eval-string s "(ns j (:require [klara.job :as job]))
                                             (:world (job/run {} (fn [] (def big (vec (range 100000))) 1)))"))]
      (is (collected? job-world)))))

(deftest L4-retain-classes
  (testing "L4.retain.classes: an unreachable candidate frees its class loader"
    (let [s (session)
          loader (weak (k/eval-string s "(ns c (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
                                          (let [o (compiler/prepare (code (fn [x] (+ x 1))))]
                                            (.getClassLoader (class (:host-fn (:candidate o)))))"))]
      (is (collected? loader)
          "generated classes are held by Clojure's soft class cache; run with -XX:SoftRefLRUPolicyMSPerMB=0"))))

(deftest L0-space-closure
  (testing "L0.space.closure: a closure captures only the locals it uses"
    (let [s (session)
          f (k/eval-string s "(let [big (vec (range 1000)) small 1] (fn [] small))")]
      (is (= 1 (count (.-env ^klara.runtime.value.Closure f)))))))

(deftest L0-space-tail
  (testing "L0.space.tail: tail recursion and recur run in bounded continuation"
    (let [s (session)]
      (is (= :done (k/eval-string s "(defn spin [n] (if (= n 0) :done (spin (dec n)))) (spin 200000)")))
      (is (= 200000 (k/eval-string s "(loop [i 0] (if (< i 200000) (recur (inc i)) i))"))))))

(defn- used-heap []
  (dotimes [_ 3] (System/gc) (Thread/sleep 30))
  (let [rt (Runtime/getRuntime)] (- (.totalMemory rt) (.freeMemory rt))))

(deftest soak
  (testing "redefine, job, prepare, install, repeat: retained heap stays flat"
    (let [s (session)
          round "(def dataset (vec (range 20000)))
                 (job/run {:budget {:steps 5000}} (fn [] (def scratch (vec (range 20000))) (score 1)))
                 (defn score [x] (+ x (count dataset)))
                 (compiler/optimize! 'soak/score)
                 (score 1)"]
      (k/eval-string s "(ns soak (:require [klara.job :as job] [klara.compiler :as compiler]))
                        (defn score [x] x)")
      (dotimes [_ 20] (k/eval-string s round))
      (let [before (used-heap)]
        (dotimes [_ 200] (k/eval-string s round))
        (let [after (used-heap)
              growth-mb (/ (- after before) 1024.0 1024.0)]
          (is (< growth-mb 16) (str "retained heap grew by " growth-mb " MB over 200 rounds"))
          (is (<= (:history-entries (klara.runtime.session/retained s)) 1000)))))))
