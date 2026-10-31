(ns klara.load-test
  (:require [clojure.test :refer [deftest is]] [klara.load :as load]
            [klara.world :as w] [klara.defs :as d] [klara.repl :as repl]
            [klara.expand :as x] [klara.stage :as stage] [klara.compile.staged]))

(def ^:dynamic *definition-expansions* nil)

(defn definition-form []
  (swap! *definition-expansions* inc)
  '(def produced 9))

(deftest top-level-macros-are-not-expanded-twice-to-classify-definitions
  (doseq [route [:loader :repl]]
    (binding [*definition-expansions* (atom 0)]
      (let [s (repl/session) wo (repl/current-world s)
            text "(defmacro produce [] (klara.load-test/definition-form)) (produce)"]
        (case route
          :loader (load/load-string! wo text)
          :repl (is (empty? (:errors (repl/eval-response s text)))))
        (is (= 1 @*definition-expansions*))
        (is (= 9 (d/lookup (w/snapshot wo) 'produced)))))))

(deftest module-aliases-and-dependent-expansions-diverge-in-forks
  (let [parent (w/make-world)
        options {:sources {'one "(ns one) (def value 1)"
                           'two "(ns two) (def value 2)"}}]
    (load/load-string! parent "(ns consumer (:require [one :as p])) (defn f [] p/value)" options)
    (let [held (d/lookup (w/snapshot parent) 'consumer/f)
          child (w/fork parent)]
      (load/load-string! child "(ns consumer (:require [two :as p]))" options)
      (is (= 2 ((d/lookup (w/snapshot child) 'consumer/f))))
      (is (= 1 ((d/lookup (w/snapshot parent) 'consumer/f))))
      (is (= 1 (held)))
      (is (= {'p 'one} (:aliases (load/descriptor (w/snapshot parent) 'consumer))))
      (is (= {'p 'two} (:aliases (load/descriptor (w/snapshot child) 'consumer)))))))

(deftest namespaces-aliases-dsl-and-staged-kernel-live-in-the-world
  (let [s (repl/session {:source-roots ["examples/compat"]}) wo (repl/current-world s)
        result (load/load-file! wo "examples/compat/demo/pipeline.cljc" {:source-roots ["examples/compat"]})
        old (w/snapshot wo) held (d/lookup old 'demo.pipeline/kernel)]
    (is (= 'demo.pipeline (:namespace result)))
    (is (= {'poly 'demo.polynomial} (:aliases (load/descriptor old 'demo.pipeline))))
    (is (= [6 11 18] ((d/lookup old 'demo.polynomial/scores) [1 2 3])))
    (is (= 27 (held 4)))
    (is (= true (:syntax? (w/entry* old 'demo.pipeline/polynomial))))
    (is (nil? (ns-resolve (create-ns 'demo.pipeline) 'kernel)) "no guest Var interned in host")
    (is (re-find #":installed" (repl/eval-string s "(demo.pipeline/refine)")))
    (is (= "27" (repl/eval-string s "(demo.pipeline/kernel 4)")))
    (load/eval-form! wo 'demo.polynomial '(def model [10]))
    (is (= 10 ((d/lookup (w/snapshot wo) 'demo.pipeline/kernel) 4)))
    (is (= 27 (held 4)))
    (is (= 27 ((d/lookup old 'demo.pipeline/score) 4)))))

(deftest namespace-context-survives-macro-invalidation
  (let [wo (w/make-world)]
    (load/load-string! wo "(ns alpha) (defmacro step [x] (list '+ x 1)) (defn f [x] (step x))")
    (load/load-string! wo "(ns beta) (defn f [x] (+ x 100))")
    (is (= 3 ((d/lookup (w/snapshot wo) 'alpha/f) 2)))
    (load/eval-form! wo 'alpha '(defmacro step [x] (list '+ x 10)))
    (is (= 12 ((d/lookup (w/snapshot wo) 'alpha/f) 2)))
    (is (= 102 ((d/lookup (w/snapshot wo) 'beta/f) 2)))))

(deftest rejected-loads-do-not-publish-partial-definitions
  (doseq [[text options] [["(ns bad) (def x 1) (unknown)" {}]
                          ["(ns bad (:import java.io.File))" {}]
                          ["(ns bad (:require [dependency :refer :all]))" {}]
                          ["(ns wrong) (def x 1)" {:expected 'right}]
                          ["(ns a (:require [b]))" {:sources {'b "(ns b (:require [a]))" 'a "(ns a (:require [b]))"}}]]]
    (let [wo (w/make-world) before (w/snapshot wo)]
      (is (thrown? Exception (load/load-string! wo text options)))
      (is (identical? before (w/snapshot wo))))))

(deftest reader-contexts-are-local-and-repl-errors-are-structured
  (let [s (repl/session)]
    (is (= "nil\n#'a/x\n3" (repl/eval-string s "(ns a) (def x #?(:klara 3 :clj 9)) x")))
    (is (= ":host" (repl/eval-string s "#?(:clj :host :klara :guest)"))
        "JVM reader retains :clj; first matching branch wins")
    (is (= ":a/key" (repl/eval-string s "::key")))
    (is (= "nil\n#'b/x\n7" (repl/eval-string s "(ns b) (def x 7) x")))
    (is (= "3" (repl/eval-string s "a/x")))
    (is (seq (:errors (repl/eval-response s "(unbound)"))))
    (is (empty? (:errors (repl/eval-response s "\"!! just data\""))))))

(deftest top-level-require-and-load-file-use-the-guest-loader
  (let [s (repl/session {:source-roots ["examples/compat"]})]
    (is (= "#'old\n3" (repl/eval-string s "(def old 3) old")))
    (is (= "nil\n[6 11]\n3"
           (repl/eval-string s "(require '[demo.polynomial :as p]) (p/scores [1 2]) old")))
    (is (re-find #"demo.pipeline/refine" (repl/eval-string s "(load-file \"examples/compat/demo/pipeline.cljc\")")))
    (is (= "27" (repl/eval-string s "(kernel 4)")))))
