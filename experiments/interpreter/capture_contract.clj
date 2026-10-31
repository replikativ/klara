;; Bounded semantic probe, not a benchmark or a production test suite.
;; Run: clojure -M experiments/interpreter/capture_contract.clj
;; Includes a private-helper inspection and guest-level multi-shot observations.
;; Ordinary free-variable liveness cannot replace current capture reachability.
(require '[klara.authority :as a]
         '[klara.defs :as d]
         '[klara.eval :as ev]
         '[klara.world :as w])

(let [world (w/make-world)
      fiber (w/fiber world)]
  (binding [ev/*fiber* fiber a/*store* (a/new-store)]
    (let [closure (d/eval-in fiber '(let [r (resource :unused)] (fn [] 42)))
          blocker (#'klara.eval/resume-blocker [{:tag :list :vals [closure]}])
          result {:probe :unused-authority-capture
                  :captured-count (count (ev/closure-locals closure))
                  :blocker blocker
                  :call-result (ev/call-value closure [])}]
      (assert (= 1 (:captured-count result)))
      (assert (re-find #"captured a resource authority" blocker))
      (assert (= 42 (:call-result result)))
      (prn result))))

(doseq [reference? [false true]]
  (let [world (w/make-world)
        fiber (w/fiber world)]
    (binding [ev/*fiber* fiber a/*store* (a/new-store)
              ev/*reference-driver* reference?]
      (let [observe (fn [form]
                      (try {:value (d/eval-in fiber form)}
                           (catch Throwable t {:error (ex-message t)})))
            ;; r exists only in f's capture, not in the enclosing handler's
            ;; lexical environment. Neither f nor the resumed body uses r.
            captured (observe
                       '(let [f ((fn [] (let [r (resource :unused)] (fn [] 42))))]
                          (handle [h {:split (fn [k] [(k :left) (k :right)])}]
                            (do (perform h :split) (f)))))
            control (observe
                      '(let [f ((fn [] (fn [] 42)))]
                         (handle [h {:split (fn [k] [(k :left) (k :right)])}]
                           (do (perform h :split) (f)))))]
        (assert (re-find #"captured a resource authority" (:error captured)))
        (assert (= {:value [42 42]} control))
        (prn {:probe :guest-unused-authority-capture
              :reference-driver reference? :captured captured :control control})))))
