(ns klara.code-identity-test
  (:require [clojure.test :refer [deftest is]]
            [klara.code :as code] [klara.core :as c]
            [klara.compile.infer-affine :as ia] [klara.compile.staged :as staged]
            [klara.eval :as ev]
            [klara.infer-affine-test :as base] [klara.stage :as stage] [klara.world :as w]))

(deftest runtime-numeric-representations-have-order-independent-identities
  (let [values [(long 1) (int 1) (bigint 1) (biginteger 1) (double 1) (float 1) 1M]
        terms (mapv #(c/lam 1 (c/quote* [% {:number %} #{%}])) values)]
    (is (= (count values) (count (set (map c/code-id terms)))))
    (is (= (mapv c/code-id terms) (mapv c/code-id (mapv identity terms))))
    (doseq [term (reverse terms)]
      (is (= (c/code-id term) (c/code-id (into {} term)))))
    (is (= (c/code-id (c/lam 1 (c/local 0)))
           (c/code-id (c/lam (int 1) (c/local (int 0)))))))
  (is (= (c/code-id (c/lam 1 (c/quote* ["x" 1N])))
         (binding [*print-readably* false *print-dup* true]
           (c/code-id (c/lam 1 (c/quote* ["x" 1N]))))))
  (is (= (c/code-id (c/quote* (sorted-map 'a 1)))
         (c/code-id (c/quote* {'a 1}))))
  (is (string? (c/code-id (sorted-map 'proof 'checked)))))

(deftest unsupported-bigint-source-does-not-enter-an-equal-long-specialization
  (let [source (base/source '(fn [n] (loop [i 0 acc [9223372036854775807]]
                                     (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc))))
        term (base/term source)
        big-term (assoc-in term [:body :body :init :datum] [(bigint Long/MAX_VALUE)])
        big-source (code/->code (code/core->s big-term)) cache (stage/make-cache)]
    (is (= term big-term) "Clojure equality is too coarse for executable identity")
    (is (not= (c/code-id term) (c/code-id big-term)))
    (staged/install! cache w/empty-root (ia/prepare w/empty-root source))
    (is (= [9223372036854775808N] (base/call big-source [1])))
    (is (= [9223372036854775808N] (stage/with-cache cache (base/call big-source [1]))))
    (is (zero? (:hits (stage/stats cache))))
    (is (= :error (first (stage/with-cache cache (base/observe #(base/call source [1]))))))))

(deftest entry-memo-does-not-reuse-a-prior-code-id-implementation
  (let [source (base/source '(fn [n] (loop [i 0 acc [0]]
                                     (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc))))
        f (ev/run (base/term source)) cache (stage/make-cache) original c/code-id]
    (staged/install! cache w/empty-root (ia/prepare w/empty-root source))
    (is (= [1] (stage/with-cache cache (ev/call-value f [1]))))
    (is (= 1 (:hits (stage/stats cache))))
    (with-redefs [c/code-id (fn [term] (str "different-version:" (original term)))]
      (is (= [1] (stage/with-cache cache (ev/call-value f [1]))))
      (is (= 1 (:hits (stage/stats cache)))))
    (is (= [1] (stage/with-cache cache (ev/call-value f [1]))))
    (is (= 2 (:hits (stage/stats cache))))))
