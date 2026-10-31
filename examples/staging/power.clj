(ns staging.power
  "Staging: programs that construct programs."
  (:require [klara.stage :refer [code esc lift run reify]]
            [klara.world :as world]))

;; The ordinary definition.
(defn power [n x]
  (if (= n 0) 1 (* x (power (dec n) x))))

;; A generator: given n now and code for x, return code for x^n.
(defn power-gen [n x]
  (if (= n 0)
    (code 1)
    (code (* (esc x) (esc (power-gen (dec n) x))))))

(def cube-code (code (fn [x] (esc (power-gen 3 (code x))))))

;; Code is a value you can look at; locals are renamed apart, globals are links.
(println cube-code)   ; #klara/code (fn [x__1] (* x__1 (* x__1 (* x__1 1))))

(def cube (run cube-code))
(assert (= 27 (cube 3)))

;; Present-stage values enter code by lift (explicitly or implicitly).
(let [k 5]
  (assert (= 8 ((run (code (fn [y] (+ y k)))) 3))))

;; Global names in code are late links: they mean whatever the running world says.
(def offset 1)
(def add-offset (code (fn [y] (+ y offset))))
(def before (world/current))
(def offset 2)
(assert (= 12 ((run add-offset) 10)))
(assert (= 11 (world/in before (fn [] ((run add-offset) 10)))))

;; reify turns a function back into code. For a function pinned to an old world
;; the links are pinned too, so the code means exactly what the function meant.
(defn offset-adder [y] (+ y offset))
(def pinned-adder (world/get (world/current) 'staging.power/offset-adder))
(def offset 3)
(assert (= 12 (pinned-adder 10)))                  ; pinned: offset = 2
(assert (= 12 ((run (reify pinned-adder)) 10)))    ; still 2, via a pinned link
(assert (= 13 ((run (reify offset-adder)) 10)))    ; open function: late link

;; Errors are data with a spec rule.
(def leaked (atom nil))
(def failure
  (try (run (code (fn [z] (esc (do (reset! leaked (code z)) (code z))))))
       (run @leaked)
       (catch Exception e (:rule (ex-data e)))))
(assert (= :L2.run.closed failure))

(println "staging: ok")
