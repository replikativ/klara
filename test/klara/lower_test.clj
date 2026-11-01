(ns klara.lower-test
  "Lowering (L4.lower.*) on terms specializers can build but the expander
  never produces."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(deftest L4-lower-steps-parallel-binding
  (testing "an inlined function called with locals of its own parameter names binds them in parallel"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= [:ready 2 2]
             (k/eval-string s "(ns lw (:require [klara.stage :refer [code run]] [klara.code :as c] [klara.compiler :as compiler]))
               (defn local [n] (c/make {:op :local :name n}))
               ;; (fn [x y] ((fn [x y] (- x y)) y x)): the inner x is the outer y
               (def candidate
                 (c/make {:op :fn :params '[x y]
                          :body (c/make {:op :app
                                         :fn (c/make {:op :fn :params '[x y]
                                                      :body (c/make {:op :app :fn (c/make {:op :host :name 'klara.core/-})
                                                                     :args [(local 'x) (local 'y)]})})
                                         :args [(local 'y) (local 'x)]})}))
               (def o (compiler/prepare (code (fn [a b] (- b a))) {:recipe (fn [_] candidate)}))
               (def f (compiler/executable o))
               [(:status o) (f 3 5) ((run candidate) 3 5)]"))))))
