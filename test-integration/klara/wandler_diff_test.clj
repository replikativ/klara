(ns klara.wandler-diff-test
  "Optional differential oracle; requires the sibling Wandler fixture."
  (:require [clojure.test :refer [deftest is]] [clojure.java.io :as io]
            [klara.fusion-test :as fixture] [klara.fusion :as f]
            [klara.fusion.kernel :as k] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

;; ---------------------------------------------------------------------------
;; differential check against wandler (needs the full Init export)
;; ---------------------------------------------------------------------------

(def init-ndjson "../wandler/test-data/init.ndjson")

(def wandler-env
  (delay
    (when (.exists (io/file init-ndjson))
      (let [parse (requiring-resolve 'ansatz.export.parser/parse-ndjson-file-streaming)
            replay (requiring-resolve 'ansatz.export.replay/replay)
            bundled (requiring-resolve 'ansatz.tactic.instance/load-bundled-instances)
            ;; Avoid slurping the 310 MB fixture plus JSON intermediates on
            ;; the capped test heap. Keep the same declarations and replay.
            decls (:final-state (parse init-ndjson [] conj))
            ke (:env (replay decls :verify? false))]
        (env/with-extension ke :instances
          (bundled {:present? #(some? (env/lookup ke (nm/from-string %)))}))))))

(defn wandler-define!
  "Define pipeline n in wandler (a/defn over (List Nat) -> Nat); returns
  [fn explain]. Requires @wandler-env."
  [n body]
  (k/proof-env)                         ; Klara's env is captured before the switch
  (reset! @(requiring-resolve 'ansatz.core/ansatz-env) @wandler-env)
  ((requiring-resolve 'wandler.core/install!))
  (let [wn (symbol (str "w-" n))
        [_ params & bd] body]
    (binding [*ns* (the-ns 'klara.wandler-diff-test)]
      (eval (list 'binding ['ansatz.core/*verbose* false]
                  (list* 'ansatz.core/defn wn [(first params) :- '(List Nat)] 'Nat bd))))
    [@(ns-resolve 'klara.wandler-diff-test wn) ((requiring-resolve 'wandler.core/explain) wn)]))

(def wandler-overrides
  "Wandler sources where its surface differs (doc/impl/S3.md §7): it does
  not elaborate reduce without init (a kernel type error on an mvar, not a
  clean rejection) and has no pos?. Same function, other spelling."
  '{plain-sum (fn [xs] (reduce + 0 xs))
    prod-small (fn [xs] (reduce * 1 (map (fn [x] (inc (rem x 3))) xs)))
    cond-map (fn [xs] (reduce + 7 (map (fn [x] (if (and (< 0 x) (<= x 50)) (quot x 2) (* 2 x))) xs)))})

(deftest differential-against-wandler
  (if-not @wandler-env
    (is false "missing oracle fixture: ../wandler/test-data/init.ndjson")
    (let [S (fixture/session-with fixture/pipelines)
          r (java.util.Random. 99)]
      (doseq [[n] fixture/pipelines] (is (= :fused (:status (f/optimize! S n)))))
      (doseq [[n body] fixture/pipelines]
        (let [[wf ex] (wandler-define! n (get wandler-overrides n body))]
          (is (:verified? ex) (str "wandler certified " n))
          (dotimes [_ 100]
            (let [xs (vec (repeatedly (.nextInt r 30) #(long (.nextInt r 100))))
                  kl (f/run S (list n xs))]
              (is (== kl (wf xs)) (str n " " xs))
              (is (= kl (f/run-generic S (list n xs)))))))))))
