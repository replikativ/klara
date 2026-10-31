(ns klara.compiler)

;; General reviewed producer. Its exact expanded source matches the bootstrap.
(defn transfer [destinations arguments]
  (loop [i 0 evaluations [] commits []]
    (if (< i (count arguments))
      (recur (inc i)
             (conj evaluations {:temporary i :expression (nth arguments i)})
             (conj commits {:destination (nth destinations i) :temporary i}))
      {:evaluations evaluations :commits commits})))

;; These generators execute now; their output contains ordinary pure Core.
(defn evaluation-code [i arguments]
  (code {:temporary (esc (lift i))
         :expression (nth (esc arguments) (esc (lift i)))}))

(defn commit-code [i destinations]
  (code {:destination (nth (esc destinations) (esc (lift i)))
         :temporary (esc (lift i))}))

(defn records-code [kind n input]
  (if (= n 0) (code [])
    (code (conj (esc (records-code kind (dec n) input))
                (esc (if (= kind :evaluations)
                       (evaluation-code (dec n) input)
                       (commit-code (dec n) input)))))))

(defn transfer-code [arity]
  (code (fn [destinations arguments]
          {:evaluations (esc (records-code :evaluations arity (code arguments)))
           :commits (esc (records-code :commits arity (code destinations)))})))

;; Staging specializes the compiler service to a known transfer arity.
(def three-code (transfer-code 3))
(def three (run three-code))

;; This ordinary world definition selects the generated compiler service.
;; The compiler invokes edited services through bounded stepping even if an
;; executable for them has separately been installed for ordinary guest calls.
(defn transfer-policy [request]
  (if (= (get request :arity) 3)
    'klara.compiler/three
    'klara.compiler/transfer))

;; Optional ordinary-call acceleration of the generated service. Installation
;; follows fork exit; it does not authorize unmetered compiler-service calls.
(defn prepare-code [source]
  (let [candidate (fork [job (perform :stage/prepare source {:backend :baseline})]
                    (adopt! job))]
    (perform :stage/install candidate)))

(defn prepare-three [] (prepare-code three-code))

;; Funding and scheduling belong to the caller; publication follows fork exit.
(defn prepare-request [subject options]
  (let [result (fork [worker (perform :stage/prepare-request subject options)]
                 (adopt! worker))]
    (if (= :prepared (get result :status))
      (perform :stage/install (get result :candidate))
      result)))
