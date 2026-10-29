(load-file "experiments/pldi/smc.clj")
(require '[klara.pldi.smc :as smc] '[klara.world :as w] '[klara.defs :as d]
         '[klara.stage :as s] '[klara.compile.core :as cc] '[klara.authority :as a])
(let [wo (w/make-world) cache (s/make-cache)
      _ (d/define! wo (list 'def 'emission smc/emission))
      _ (doseq [form smc/forms] (d/define! wo form))
      f (d/lookup (w/snapshot wo) 'smc)
      _ (s/install! cache (cc/compile-def wo 'emission))
      samples (mapv (fn [seed]
                      (let [run #(binding [a/*store* (a/new-store)] (f smc/ys 64 seed))
                            generic (run) compiled (s/with-cache cache (run))]
                        (assert (= generic compiled) [seed generic compiled])
                        {:seed seed :particles 64 :result generic})) (range 1 17))
      emission (eval smc/emission)
      exact (loop [obs smc/ys rain 0.5 dry 0.5 z 1.0]
              (let [lik (fn [p] (let [q (emission p 16)] (if (first obs) q (- 1.0 q))))
                    r (* rain (lik 0.9)) d (* dry (lik 0.2)) total (+ r d)
                    r (/ r total) d (/ d total) z (* z total)]
                (if (next obs)
                  (recur (next obs) (+ (* 0.8 r) (* 0.2 d)) (+ (* 0.2 r) (* 0.8 d)) z)
                  {:p-true r :z z})))
      run-model (fn [model]
                  (d/define! wo (list 'def 'model model))
                  (binding [a/*store* (a/new-store)]
                    ((d/lookup (w/snapshot wo) 'smc) smc/ys 32 42)))
      _ (assert (= [0 1.0] (run-model '(fn [m ys] false))))
      _ (assert (= [0 1.0] (run-model '(fn [m ys] nil))))
      _ (assert (= [0 1.0] (run-model '(fn [m ys] (do (perform m :observe 1.0 true) false)))))
      error (fn [form] (try (run-model form) :unexpected-success (catch Exception e (ex-message e))))
      zero-error (error '(fn [m ys] (do (perform m :observe 0.0 true) false)))
      mixed-error (error '(fn [m ys] (if (perform m :choose 0.5) false
                                     (do (perform m :observe 0.9 true) false))))
      mean-p (/ (reduce + (map #(/ (first (:result %)) 64.0) samples)) 16)
      mean-z (/ (reduce + (map #(second (:result %)) samples)) 16)
      result {:samples samples :exact exact :mean-p-true mean-p :mean-z mean-z
              :absolute-p-error (Math/abs (- mean-p (:p-true exact)))
              :relative-z-error (/ (Math/abs (- mean-z (:z exact))) (:z exact))
              :completion-results [false nil] :zero-mass zero-error :mixed-boundaries mixed-error}]
  (assert (= "zero particle mass" zero-error))
  (assert (= "mixed observation boundaries" mixed-error))
  (spit (str (first *command-line-args*) "/smc-validation.edn") (pr-str result))
  (prn result))
(shutdown-agents)
