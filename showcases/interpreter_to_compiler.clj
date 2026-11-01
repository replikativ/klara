(ns showcases.interpreter-to-compiler
  "An interpreter becomes a compiler at run time.

  `calc` is a plain interpreter for arithmetic expressions. `calc-gen` is
  its staged twin: the same structure, but it writes code instead of
  computing. The specializer attached to `calc` waits until the profile shows
  that `calc` keeps receiving the same expression, then asks the JIT to
  replace `calc` by the generated code for that expression, guarded on the
  expression staying the same. The kernel admits the replacement only after
  checking that it means exactly what the interpreter means for that
  expression: the first Futamura projection, checked."
  (:require [klara.stage :refer [code esc lift]]
            [klara.jit :as jit]
            [klara.compiler :as compiler]))

;; The staged twin: expression known now, environment known later.
(defn calc-gen [expr env]
  (cond (number? expr) (lift expr)
        (keyword? expr) (code (get (esc env) (esc (lift expr))))
        :else (let [[op a b] expr]
                (case op
                  :+ (code (+ (esc (calc-gen a env)) (esc (calc-gen b env))))
                  :* (code (* (esc (calc-gen a env)) (esc (calc-gen b env))))
                  :- (code (- (esc (calc-gen a env)) (esc (calc-gen b env))))))))

;; A user-written JIT strategy for calc.
(defn calc-specializer [ctx default]
  (if (and (jit/stable? ctx 0) (> (jit/calls ctx) 100))
    (let [expr (jit/stable-value ctx 0)]
      (jit/function ctx
        (fn [e env]
          (jit/guard (code (jit/same? (esc e) (esc (lift expr))))   ; still the same expression?
                     (calc-gen expr env)                             ; then: our generated code
                     (jit/reference-body ctx e env)))))              ; else: the interpreter
    (default ctx)))

;; The interpreter: ordinary Clojure.
(defn ^{:klara/specialize calc-specializer} calc [expr env]
  (cond (number? expr) expr
        (keyword? expr) (get env expr)
        :else (let [[op a b] expr]
                (case op
                  :+ (+ (calc a env) (calc b env))
                  :* (* (calc a env) (calc b env))
                  :- (- (calc a env) (calc b env))))))

;; The same, but forgetting the guard: wrong for every other expression.
(defn unguarded-specializer [ctx default]
  (let [expr (jit/stable-value ctx 0)]
    (jit/function ctx (fn [e env] (calc-gen expr env)))))

(def model [:+ [:* :x :x] [:- [:* 3 :y] 7]])

(defn run [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (calc model {:x i :y 2}))) acc)))

(defn ms [f] (let [t (System/nanoTime) r (f)] [(/ (- (System/nanoTime) t) 1000000.0) r]))

(run 200)                                                      ; the driver's profile: a few iterations
(compiler/optimize! 'showcases.interpreter-to-compiler/run)   ; the driver loop is compiled in both runs
(dotimes [_ 3] (run 20000))
(def interpreted (ms #(run 20000)))
(def unguarded (jit/compile! 'showcases.interpreter-to-compiler/calc {:specializer unguarded-specializer}))
(def outcome (jit/compile! 'showcases.interpreter-to-compiler/calc))
(dotimes [_ 3] (run 20000))
(def compiled (ms #(run 20000)))
(def other (calc [:+ :x 1] {:x 41}))       ; a different expression: the guard fails, the interpreter answers

;; Static where we can: `run` always passes the definition `model`, so
;; compiling `run` specializes the call to it. No guard, no call; `model`'s
;; generation is a premise of the compiled `run`.
(def driver (jit/compile! 'showcases.interpreter-to-compiler/run))
(dotimes [_ 3] (run 20000))
(def specialized (ms #(run 20000)))

(def report
 {:status (:status outcome)
 :evidence (:evidence outcome)
 :speculations (:speculations outcome)
 :checked-in-steps (:steps (:spent outcome))
 :same-result (= (second interpreted) (second compiled))
 :interpreted-ms (first interpreted)
 :compiled-ms (first compiled)
 :other-expression other
 :speedup (Math/round (/ (first interpreted) (first compiled)))
 :unguarded (:status unguarded)
 :driver (:status driver)
 :driver-premises (mapv first (:premises driver))
 :specialized-ms (first specialized)
 :same-specialized (= (second interpreted) (second specialized))})

(doseq [k [:status :evidence :speculations :checked-in-steps :same-result
           :interpreted-ms :compiled-ms :speedup :other-expression :unguarded
           :driver :driver-premises :specialized-ms :same-specialized]]
  (println (str (name k) ":") (get report k)))

report
