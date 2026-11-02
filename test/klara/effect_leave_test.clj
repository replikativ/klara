(ns klara.effect-leave-test
  "perform and handle in compiled code leave to the interpreter (L4.exec.leave):
  generators, multi-shot resumption, try around a perform, handlers installed
  by compiled code, compiled functions under interpreted handlers, jobs and
  budgets give the interpreter's values and steps, also leaving everywhere."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.lower :as lower]
            [klara.host.api :as k]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(def ^:private program
  "(ns el (:require [klara.compiler :as compiler] [klara.effect :refer [perform handle]] [klara.job :as job]))
   (defn gen [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (perform :next i))) acc)))
   (defn run-gen [n] (handle {:next (fn [k i] (k (* i i)))} (gen n)))
   ;; multi-shot: every choice point resumed twice
   (defn bits [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (if (perform :amb) 1 0))) acc)))
   (defn all-bits [n] (handle {:amb (fn [k] (into (k true) (k false))) :return (fn [x] [x])} (bits n)))
   ;; try around a perform; an exception after resumption is caught by the same try
   (defn guarded [x] (try (let [v (perform :ask x)] (if (neg? v) (throw (ex-info \"neg\" {:v v})) (* 2 v)))
                          (catch clojure.lang.ExceptionInfo e [:caught (:v (ex-data e))])
                          (finally (inc x))))
   (defn run-guarded [] [(handle {:ask (fn [k x] (k x))} (guarded 4))
                         (handle {:ask (fn [k x] (k (- x)))} (guarded 4))
                         (handle {:ask (fn [k x] [(k 1) (k -1)])} (guarded 4))])
   ;; the function installs the handler itself; the handlers are compiled closures
   (defn counter [n] (handle {:tick (fn [k i] (fn [s] ((k s) (+ s i))))
                              :return (fn [x] (fn [s] [x s]))}
                       (loop [i 0] (if (< i n) (do (perform :tick i) (recur (inc i))) :end))))
   (defn run-counter [n] ((counter n) 0))
   ;; a handler that resumes twice, not in tail position
   (defn both [] (handle {:flip (fn [k] (+ (k 1) (k 10)))} (let [a (perform :flip) b (perform :flip)] (* a b))))
   ;; a compiled closure that performs, called by interpreted code under a handler
   (defn mk [] (fn [x] (+ x (perform :ask))))
   (defn use-mk [] (handle {:ask (fn [k] (k 100))} ((mk) 1)))
   (defn unhandled [] (perform :nobody))
   (defn in-job [n] (job/run {:budget {:steps 100000}} (fn [] (run-gen n))))
   (defn uses [] [(run-gen 100) (all-bits 3) (run-guarded) (run-counter 50) (both) (use-mk)
                  (:value (in-job 200))
                  (try (unhandled) (catch Exception e (:rule (ex-data e))))])")

(def ^:private names '[el/gen el/bits el/guarded el/counter el/both el/mk el/unhandled])

(deftest perform-and-handle-leave   ; L4.exec.leave L4.lower.subset L4.lower.calls L4.exec.osr L4.lower.steps
  (let [s (session)]
    (k/eval-string s program)
    (let [interpreted (k/eval-string s "(el/uses)")
          steps (k/eval-string s "(:steps (:spent (el/in-job 200)))")]
      (is (= [:ready] (distinct (k/eval-string s (str "(mapv (comp :status compiler/optimize!) '" names ")")))))
      (is (= interpreted (k/eval-string s "(el/uses)")))
      (testing "the compiled paths left and re-entered the loops"
        (is (= :left (k/eval-string s "(do (el/run-gen 10) (:last-path (compiler/explain el/gen)))")))
        (is (pos? (k/eval-string s "(:reentries (compiler/explain el/gen))"))))
      (testing "steps are charged as interpreted, within the per-entry difference"
        (let [c (k/eval-string s "(:steps (:spent (el/in-job 200)))")]
          (is (<= (Math/abs (- c steps)) 10) [steps c])))
      (testing "leaving at every function entry gives the same values"
        (reset! lower/stress 1.0)
        (try (is (= interpreted (k/eval-string s "(el/uses)")))
             (finally (reset! lower/stress nil)))))))
