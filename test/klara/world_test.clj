(ns klara.world-test
  "Unit checks for world publication and slices."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]
            [klara.runtime.world :as w]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(deftest L1-session-conflict
  (testing "L1.session.conflict: two proposals changing the same name"
    (let [s (session)]
      (k/eval-string s "(ns p (:require [klara.world :as world])) (def x 1)
                        (def a (world/define (world/current) 'p/x 2))
                        (def b (world/define (world/current) 'p/x 3))
                        (world/publish! a)")
      (is (= :L1.session.conflict
             (try (k/eval-string s "(world/publish! b)") nil
                  (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))))))

(deftest L1-session-publish-disjoint
  (testing "L1.session.publish: proposals changing different names both apply"
    (let [s (session)]
      (is (= [2 20] (k/eval-string s "(ns q (:require [klara.world :as world])) (def x 1) (def y 10)
                                       (def a (world/define (world/current) 'q/x 2))
                                       (def b (world/define (world/current) 'q/y 20))
                                       (world/publish! a) (world/publish! b) (world/advance) [x y]"))))))

(deftest L1-slice-missing
  (testing "L1.slice.missing: a slice refuses names outside its footprint"
    (let [s (session)
          _ (k/eval-string s "(ns r) (def a 1) (def b 2)")
          slice (w/slice (:world @s) #{'r/a})]
      (is (= 1 (:value (w/lookup slice 'r/a))))
      (is (= :L1.slice.missing (try (w/lookup slice 'r/b) nil
                                    (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))))))
