(ns kmap.run-all
  (:require [clojure.test :as t] [clojure.pprint]
            [kmap.core :as k]
            kmap.core-test kmap.champ-test kmap.trap))

(defn -main [& _]
  (println "== backend :phm")
  (let [a (t/run-tests 'kmap.core-test)
        _ (println "== backend :champ")
        b (binding [k/*backend* :champ] (t/run-tests 'kmap.core-test 'kmap.champ-test))]
    (println "== interface-omission probe (kmap.trap)")
    (clojure.pprint/pprint (kmap.trap/report))
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail a) (:error a) (:fail b) (:error b))) 0 1))))
