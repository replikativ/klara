;; One persistent REPL: builds artifacts, then loads them with compiler functions disabled.
(load-file "experiments/typed_jit/regions.clj")
(load-file "experiments/typed_jit/aot.clj")
(require '[klara.region-aot :as aot] '[klara.compile.requirements :as requirements]
         '[klara.world :as w] '[klara.defs :as d] '[klara.eval :as ev]
         '[klara.compile.core :as cc] '[klara.typed-regions :as regions]
         '[clojure.edn :as edn])

(def aot-check-count (atom 0))
(defn aot-check! [pred label]
  (assert pred (str "AOT check failed: " label))
  (swap! aot-check-count inc))
(defn aot-outcome [f]
  (try [:value (f)] (catch Throwable e [:error (class e) (.getMessage e)])))

(def aot-world (w/make-world))
(d/define! aot-world '(def g (fn [x] (* x 2))))
(d/define! aot-world '(def f (fn [n] (loop [i n s 0]
                                     (if (> i 0) (recur (dec i) (+ s (g i))) s)))))
(def aot-old-root (w/snapshot aot-world))
(def aot-file "/tmp/klara-s22-old.edn")
(def aot-build-result (aot/build! aot-old-root aot-file))
(def aot-original-artifact (edn/read-string (slurp aot-file)))

;; Compile calls here would fail; loading only validates and defines saved class bytes.
(def aot-loaded
  (with-redefs [cc/compile-def (fn [& _] (throw (Exception. "unexpected compile")))
                regions/typed-function (fn [& _] (throw (Exception. "unexpected analysis")))
                aot/build! (fn [& _] (throw (Exception. "unexpected build")))]
    (let [loaded (aot/load! aot-file aot-old-root)]
      (aot-check! (= :loaded (:status loaded)) :load-without-compiler)
      (aot-check! (= 420 (aot/invoke! loaded aot-old-root [20])) :run-without-compiler)
      loaded)))

(doseq [n (concat (range -2 16) [Long/MAX_VALUE 2.0 2N "bad"])]
  (aot-check! (= (aot-outcome #((d/lookup aot-old-root 'f) n))
                 (aot-outcome #(aot/invoke! aot-loaded aot-old-root [n])))
              [:t0-agreement n]))
(aot-check! (= 3 (:fallback @(:stats aot-loaded))) :non-long-fallbacks)
(aot-check! (= (aot-outcome #(ev/call-value (d/lookup aot-old-root 'f) []))
               (aot-outcome #(aot/invoke! aot-loaded aot-old-root []))) :arity-fallback)
(aot-check! (not (requirements/call-valid?
                 (first (:requirements aot-loaded)) [20]
                 [[{:tag :handle :mode :dynamic :clauses {:exn/raise :test-clause}}]]))
            :handler-admission)

;; A fresh recorder must see reads even after a previous invocation used the same root.
(let [reads (atom #{})]
  (dotimes [_ 2]
    (reset! reads #{})
    (binding [w/*reads* reads] (aot/invoke! aot-loaded aot-old-root [20]))
    (aot-check! (= (:reads aot-loaded) @reads) :read-recording)))

(d/define! aot-world '(def g (fn [x] (* x 3))))
(def aot-new-root (w/snapshot aot-world))
(aot-check! (= :world-mismatch (:reason (aot/load! aot-file aot-new-root))) :stale-load)
(aot-check! (= 630 (aot/invoke! aot-loaded aot-new-root [20])) :stale-runtime-fallback)
(aot-check! (= 420 (aot/invoke! aot-loaded aot-old-root [20])) :old-root-still-valid)
(def aot-new-build (aot/build! aot-new-root "/tmp/klara-s22-new.edn"))
(def aot-new-loaded (aot/load! "/tmp/klara-s22-new.edn" aot-new-root))
(aot-check! (= 630 (aot/invoke! aot-new-loaded aot-new-root [20])) :new-specialization)
(d/define! aot-world '(def unrelated 77))
(aot-check! (= :loaded (:status (aot/load! "/tmp/klara-s22-new.edn" (w/snapshot aot-world))))
            :unrelated-publication)
(d/define! aot-world '(def f (fn [n] 42)))
(aot-check! (= :world-mismatch (:reason (aot/load! "/tmp/klara-s22-new.edn" (w/snapshot aot-world))))
            :caller-changed)
(aot-check! (= 42 (aot/invoke! aot-new-loaded (w/snapshot aot-world) [20])) :caller-fallback)

(doseq [[label modify expected]
        [[:compiler #(assoc % :compiler-id "stale") :compiler-mismatch]
         [:target #(assoc-in % [:target :java-feature] 1) :target-mismatch]
         [:format #(assoc % :format :unknown) :format-mismatch]
         [:class #(assoc-in % [:classes 1 :sha256] "corrupt") :class-integrity-mismatch]
         [:reads #(assoc % :reads #{}) :read-set-mismatch]
         [:requirements #(assoc-in % [:requirements 0 :inputs] [:double]) :bad-requirements]]]
  (spit "/tmp/klara-s22-bad.edn" (pr-str (modify aot-original-artifact)))
  (aot-check! (= expected (:reason (aot/load! "/tmp/klara-s22-bad.edn" aot-old-root))) label))
(spit "/tmp/klara-s22-bad.edn" "{unclosed")
(aot-check! (= :invalid-artifact (:reason (aot/load! "/tmp/klara-s22-bad.edn" aot-old-root))) :bad-edn)

(def aot-result {:checks @aot-check-count :build aot-build-result
                 :load-ms (:load-ms aot-loaded) :new-build aot-new-build
                 :old-stats @(:stats aot-loaded) :new-stats @(:stats aot-new-loaded)})
(spit "experiments/typed_jit/s22-results.edn" (pr-str aot-result))
(println :aot-checks-passed aot-result)
