(ns effects.jobs
  "Effects and jobs: run a change in isolation, then decide."
  (:require [klara.effect :refer [perform handle]]
            [klara.job :as job]))

;; Handlers give meaning to effects. k resumes the computation.
(assert (= [:asked 42]
           (handle {:demo/ask (fn [k q] (k [:asked q]))}
             (perform :demo/ask 42))))

;; Continuations are multi-shot: resume twice, collect both answers.
(assert (= [1 2]
           (handle {:demo/choose (fn [k] [(k 1) (k 2)])}
             (perform :demo/choose))))

(def price 10)
(defn quote-for [n] (* n price))

;; A job runs in a fork of the world under a budget. Nothing leaks out.
(def outcome
  (job/run {:budget {:steps 10000}}
    (fn []
      (def price 7)
      (println "trying price 7")       ; deferred, not printed
      (quote-for 3))))

(assert (= :done (:status outcome)))
(assert (= 21 (:value outcome)))
(assert (= 30 (quote-for 3)))          ; the session is unchanged
(assert (= [[:io/print "trying price 7\n"]] (:intents outcome)))

;; Adopting publishes the job's world and performs its intents.
(job/adopt! outcome)                   ; prints "trying price 7"
(assert (= 21 (quote-for 3)))

;; Budgets stop runaway computations; the outcome can be resumed.
(defn spin [n] (if (= n 0) :finished (spin (dec n))))
(def partial (job/run {:budget {:steps 100}} (fn [] (spin 1000))))
(assert (= :exhausted (:status partial)))
(def finished (job/resume partial {:steps 100000}))
(assert (= :finished (:value finished)))

(println "jobs: ok")
