(ns klara.staging-test
  "Unit checks for staging internals that no surface program reaches yet."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]
            [klara.runtime.machine :as m]
            [klara.runtime.world :as w]))

(deftest L2-link-guarded
  (testing "L2.link.guarded: the recorded value while the generation matches, the late value after"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})
          _ (k/eval-string s "(ns g) (def k 1)")
          world (:world @s)
          gen (w/generation world 'g/k)
          link {:kind :guarded :name 'g/k :generation gen :value 1}]
      (is (= 1 (m/resolve-link link world)))
      (k/eval-string s "(def k 2)")
      (is (= 2 (m/resolve-link link (:world @s))))
      (is (= 1 (m/resolve-link link world)) "an older world still satisfies the guard"))))

(deftest L2-print-form
  (testing "L2.print.form: links print by kind"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= "#klara/code (fn [x__1] (+ x__1 g/k))"
             (-> (k/eval-string s "(ns g (:require [klara.stage :refer [code]])) (def k 1) (pr-str (code (fn [x] (+ x k))))")
                 (clojure.string/replace #"x__\d+" "x__1")))))))
