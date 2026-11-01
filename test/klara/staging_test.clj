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

(deftest recur-crosses-holes   ; L2.code.recur L2.code.extrusion
  (testing "a recur built in a hole re-enters the template's loop; out of its loop's construction it is extruded"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= [5 :L2.code.extrusion]
             (k/eval-string s "(ns rc (:require [klara.stage :refer [code esc run]]))
               ;; the helper splices a recur it did not build: the loop's
               (defn while-below [j n again] (code (if (< (esc j) (esc n)) (esc again) (esc j))))
               (def counted (code (loop [j 0] (esc (while-below (code j) (code 5) (code (recur (inc j))))))))
               (def saved (atom nil))
               (code (loop [j 0] (esc (do (reset! saved (code (recur (inc j)))) (code j)))))
               [(run counted)
                (try (code (fn [] (esc @saved))) (catch Exception e (:rule (ex-data e))))]")))
      (is (= :L2.stage.level
             (try (k/eval-string s "(ns rc) (fn [j] (code (recur (inc (esc j)))))")
                  (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))))))
