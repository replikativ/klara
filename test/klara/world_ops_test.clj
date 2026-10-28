(ns klara.world-ops-test
  "The ambient world operations registered by klara.defs: :world/fork,
  :world/fiber, :world/eval-in, :world/call-in, :world/invalidate."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]))

(defn- session []
  (let [wo (w/make-world)] {:world wo :fiber (w/fiber wo)}))

(defn- k!
  "Evaluate or define form in the session, as a REPL does: raise the
  session fiber to the newest root first."
  [{:keys [world fiber]} form]
  (w/raise-basis! fiber)
  (binding [ev/*fiber* fiber]
    (if (and (seq? form) ('#{def defn defmacro} (first form)))
      (:name (d/define! world form))
      (d/eval-in fiber form))))

(deftest fork-is-a-snapshot
  (let [s (session)]
    (k! s '(defn step [x] (+ x 1)))
    (k! s '(def fk (perform :world/fork)))
    (is (= 'step (k! s '(perform :world/eval-in fk (quote (defn step [x] (* x 2)))))))
    (is (= [2 2] (k! s '[(step 1) (perform :world/eval-in fk (quote (step 1)))])))
    (k! s '(defn step [x] (+ x 100)))
    (is (= [101 2] (k! s '[(step 1) (perform :world/eval-in fk (quote (step 1)))]))
        "parent writes after the fork are invisible in the fork, and vice versa")))

(deftest a-fiber-keeps-its-basis-until-it-raises
  (let [s (session)]
    (k! s '(defn step [x] (+ x 1)))
    (k! s '(defn sim [g x]
             (let [cmd (perform g :yield x)]
               (when (= cmd :raise) (perform :world/raise-basis))
               (sim g ((perform :world/resolve (quote step)) x)))))
    (k! s '(def fib (perform :world/fiber)))
    (k! s '(def p (perform :world/call-in fib
                           (fn [] (handle [g {:yield (fn [x k] {:state x :k k})}] (sim g 0))))))
    (is (= 0 (k! s '(:state p))))
    (k! s '(def p (perform :world/call-in fib (:k p) :go)))
    (is (= 1 (k! s '(:state p))))
    (k! s '(defn step [x] (+ x 10)))
    (k! s '(def p (perform :world/call-in fib (:k p) :go)))
    (is (= 2 (k! s '(:state p))) "still pinned: the old step")
    (k! s '(def p (perform :world/call-in fib (:k p) :raise)))
    (is (= 12 (k! s '(:state p))) "raised at the safe point: the new step")))

(deftest invalidate-from-klara
  (let [s (session)]
    (k! s '(defmacro twice [e] (qq (+ ~e ~e))))
    (k! s '(defn f [x] (twice x)))
    (k! s '(defmacro twice [e] (qq (* ~e ~e))))
    (is (= :pending (:klara/error (ex-data (try (k! s '(f 3)) (catch Exception e e))))))
    (is (= '[f] (:stale (k! s '(perform :world/invalidate (quote twice))))))
    (is (= 9 (k! s '(f 3))))))

(deftest world-ops-need-a-fiber
  (is (thrown-with-msg? Exception #"no fiber"
                        (ev/run (klara.expand/expand-expr '(perform :world/fiber) w/empty-root)))))
