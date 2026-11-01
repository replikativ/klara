(ns klara.own-test
  "Functional but in place (L4.check.in-place)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.lower :as lower]
            [klara.host.api :as k]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(def ^:private program
  "(ns ow (:require [klara.jit :as jit] [klara.own :as own] [klara.compiler :as compiler]
                    [klara.effect :refer [perform handle]]))
   (defn freqs [ws] (loop [i 0 counts {}]
                      (if (< i (count ws))
                        (let [w (nth ws i)] (recur (inc i) (assoc counts w (inc (get counts w 0)))))
                        counts)))
   (defn weight [m] (count m))
   (defn leaky [ws] (loop [i 0 counts {}]
                      (if (< i (count ws))
                        (let [w (nth ws i)] (recur (inc i) (assoc counts w (+ (get counts w 0) (weight counts)))))
                        counts)))
   (defn pick [] (perform :pick))
   (defn collect [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (+ i (pick)))) acc)))
   (def ws (vec (for [i (range 1000)] (str \"w\" (mod i 13)))))
   (freqs ws) (leaky ws)
   (def both (fn [k] [(k 0) (k 100)]))
   (def before (handle {:pick both} (collect 3)))
   (def in-place {:specializer own/in-place :certificate {:kind :in-place}})")

(deftest L4-check-in-place
  (let [s (session)]
    (k/eval-string s program)
    (testing "a linear accumulator is owned: admitted by the judgment and the erasure"
      (is (= [:ready :in-place true]
             (k/eval-string s "(def o (jit/compile! 'ow/freqs in-place))
                               [(:status o) (:evidence o) (= (freqs ws) (frequencies ws))]"))))
    (testing "an accumulator passed to another function is refused"
      (is (= :rejected (k/eval-string s "(:status (jit/compile! 'ow/leaky in-place))"))))
    (testing "leaving owned code freezes the accumulator: a continuation resumed twice sees no mutation"
      (is (= [:ready true]
             (k/eval-string s "(def o (jit/compile! 'ow/collect in-place))
                               [(:status o) (= before (handle {:pick both} (collect 3)))]"))))))

(deftest L4-check-in-place-under-stress
  (testing "owned loops left at random points compute what the interpreter computes"
    (let [s (session)]
      (k/eval-string s program)
      (k/eval-string s "(jit/compile! 'ow/freqs in-place)")
      (reset! lower/stress 0.5)
      (try
        (is (= #{true} (set (k/eval-string s "(vec (for [_ (range 20)] (= (freqs ws) (frequencies ws))))"))))
        (finally (reset! lower/stress nil))))))
