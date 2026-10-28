(ns klara.spec.run-tests
  "Kernel-checks the whole development (loading klara.spec.props re-checks
  every proof), then runs test/klara/spec/programs.edn through the compiled
  reference step function."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [klara.spec.core]
            [klara.spec.ws]
            [klara.spec.props]
            [klara.spec.interp :as interp]))

(defn load-programs []
  (edn/read-string (slurp (io/resource "klara/spec/programs.edn"))))

(defn run-program [{:keys [program world]}]
  (dissoc (interp/run program (or world {})) :steps))

(defn -main [& _]
  (let [results (for [{:keys [name expect] :as p} (load-programs)]
                  (let [actual (run-program p)]
                    {:name name :ok (= expect actual) :expect expect :actual actual}))
        failed (remove :ok results)]
    (doseq [{:keys [name ok actual]} results]
      (println (if ok "ok  " "FAIL") name actual))
    (println (count results) "programs," (count failed) "failed")
    (shutdown-agents)
    (System/exit (if (seq failed) 1 0))))
