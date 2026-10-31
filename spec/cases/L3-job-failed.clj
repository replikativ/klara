;; rules: L3.job.outcome
;; expect: [:failed "bad" :demo/bad]
(ns e7 (:require [klara.job :as job]))
(let [o (job/run {} (fn [] (throw (ex-info "bad" {:rule :demo/bad}))))]
  [(:status o) (get-in o [:error :message]) (get-in o [:error :rule])])
