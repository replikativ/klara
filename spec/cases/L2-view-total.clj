;; rules: L2.view.total
;; expect: [[:fn :letrec :throw :try :interop :def] [2 "R" 7] [true true true true]]
(ns vt (:require [klara.stage :refer [code run]] [klara.code :as c] [klara.compiler :as compiler]))
(defn defines [] (def vt-x 1))
(def cs [(code (fn ([x] x) ([x & r] r)))
         (code (letfn [(f [x] x)] (f 1)))
         (code (throw (ex-info "x" {})))
         (code (try 1 (catch Exception e 2) (finally 3)))
         (code (.toUpperCase "r"))
         (:body (c/view (compiler/reference 'vt/defines)))])   ; def comes from a definition, not a template
(def ops (mapv #(:op (c/view %)) cs))
;; rebuilt from their views, with one child replaced, they still run
(def f (run (c/make (c/view (first cs)))))
(def t (c/view (nth cs 3)))
(def try2 (run (c/make (assoc t :body (code 7)))))
[ops [(count (f 1 2 3)) (run (c/make (c/view (nth cs 4)))) try2]
 (mapv #(= (:op (c/view (c/make (c/view %)))) (:op (c/view %))) [(nth cs 0) (nth cs 1) (nth cs 3) (nth cs 4)])]
