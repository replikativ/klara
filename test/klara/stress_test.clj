(ns klara.stress-test
  "Frame states under stress (L4.exec.frame-state): generated programs run
  with every definition compiled and compiled code forced to leave at random
  function entries must observe exactly what plain interpretation observes."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [klara.compile.lower :as lower]
            [klara.formal.gen :as gen]
            [klara.host.api :as k]
            [klara.lang.expand :as ex]
            [klara.runtime.session :as session]))

(defn- observe [f]
  (try (let [v (f)]
         (cond (or (fn? v) (instance? clojure.lang.IFn v)) (if (coll? v) [:value v] :fn)
               (instance? klara.runtime.value.Code v) [:code (str/replace (pr-str v) #"__\d+" "")]
               :else [:value v]))
       (catch Throwable e
         [:error (or (:rule (ex-data e)) (.getName (class e)))])))

(defn- run-program [src compile?]
  (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})
        _ (k/eval-string s "(ns gen-host (:require [klara.compiler]))")
        r (clojure.lang.LineNumberingPushbackReader. (java.io.StringReader. src))]
    (loop [out []]
      (let [form (ex/read-all r (:ns @s))]
        (if (ex/eof? form)
          out
          (let [o (observe #(session/eval-form s form))]
            (when (and compile? (seq? form) (= 'defn (first form)))
              (k/eval-string s (str "(klara.compiler/optimize! '" (:ns @s) "/" (second form) ")")))
            (recur (if (and (seq? form) (#{'ns 'defn} (first form))) out (conj out o)))))))))

(defn- run-specialized
  "Run the program, then compile every definition with the default
   specializer at thresholds that make it act on these small profiles, then
   run the program's expressions again."
  [src]
  (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})
        _ (k/eval-string s "(ns gen-host (:require [klara.jit]))")
        forms (let [r (clojure.lang.LineNumberingPushbackReader. (java.io.StringReader. src))]
                (loop [fs []] (let [f (ex/read-all r (:ns @s))] (if (ex/eof? f) fs (recur (conj fs f))))))
        expr? #(not (and (seq? %) (#{'ns 'defn} (first %))))]
    (doseq [f forms] (observe #(session/eval-form s f)))
    (doseq [f forms :when (and (seq? f) (= 'defn (first f)))]
      (observe #(k/eval-string s (str "(klara.jit/compile! '" (:ns @s) "/" (second f)
                                      " {:policy {:hot 1 :rare 1 :small 200 :large 2000}})"))))
    (mapv #(observe (fn [] (session/eval-form s %))) (filter expr? forms))))

(def seeds (or (some-> (System/getenv "KLARA_STRESS_SEEDS") parse-long) 300))

(deftest generated-programs-under-stress
  (reset! lower/stress 0.5)
  (try
    (let [mismatches (for [seed (range seeds)
                           :let [src (gen/program seed)
                                 plain (run-program src false)
                                 compiled (run-program src true)]
                           :when (not= plain compiled)]
                       {:seed seed :plain plain :compiled compiled})]
      (is (empty? (take 3 mismatches)) (pr-str (take 3 mismatches))))
    (finally (reset! lower/stress nil))))

(deftest generated-programs-specialized
  ;; the default specializer, aggressively: cold-branch speculation,
  ;; specialization of known calls, inlining (L4.jit.*, L4.check.speculate-assume)
  (reset! lower/stress 0.3)
  (try
    (let [mismatches (for [seed (range seeds)
                           :let [src (gen/program seed)
                                 plain (run-program src false)
                                 specialized (run-specialized src)]
                           :when (not= plain specialized)]
                       {:seed seed :src src :plain plain :specialized specialized})]
      (is (empty? (take 3 mismatches)) (pr-str (take 2 mismatches))))
    (finally (reset! lower/stress nil))))
