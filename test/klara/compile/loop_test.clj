(ns klara.compile.loop-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.loop :as loops] [klara.compile.ir :as ir]
            [klara.compile.scalar :as scalar] [klara.compile.unbox :as unbox]
            [klara.compile.staged :as staged]
            [klara.code :as code] [klara.defs :as d] [klara.eval :as ev]
            [klara.expand :as x] [klara.stage :as stage] [klara.world :as w]))

(defn loop-node [form]
  (first (filter #(= :letrec (:op %)) (ir/nodes (ir/named (x/expand-expr form w/empty-root))))))
(def sample '(fn [n] (loop [i 0 a 1 b 2] (if (< i n) (recur (+ i 1) b (+ a b)) a))))
(defn check-of [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (:check (ex-data ex)))))

(deftest structural-view-keeps-origins-and-arbitrary-tail-transfers
  (let [node (loop-node sample) view (loops/inspect! node)
        edge (first (:backedges view))]
    (is (identical? node (:source view)))
    (is (identical? (:node edge) (get-in node (:path edge))))
    (is (= 3 (count (:parameters view))))
    (is (= [:inits 0 :body :then] (:path edge)))
    (is (= (get-in node [:inits 0 :body :then :args])
           (mapv :expression (get-in edge [:transfer :evaluations])))))
  (let [node (loop-node '(fn [n] (loop [i n a 1 b 2]
                                   (if (> i 0)
                                     (if (< a b) (recur (- i 2) b (+ a b)) (recur (- i 3) a b))
                                     (+ a b)))))
        view (loops/inspect! node)]
    (is (= 2 (count (:backedges view))))
    (is (= 1 (count (:exits view))))
    (is (some #{:long} (unbox/loop-kinds node {})))))

(deftest self-calls-must-not-escape-or-cross-control-boundaries
  (let [node (loop-node sample) self (:self (loops/inspect! node))
        edge (get-in node [:inits 0 :body :then])
        replace-body #(assoc-in node [:inits 0 :body] %)]
    (is (= :non-tail-self-call
           (check-of #(loops/inspect! (replace-body {:op :prim :name '+ :args [edge {:op :quote :datum 1}]})))))
    (is (= :escaping-self (check-of #(loops/inspect! (replace-body {:op :local :name self})))))
    (doseq [barrier [{:op :fn :arity 0 :rest? false :params [] :body edge}
                    {:op :code :body edge}
                    {:op :handle :clauses {} :return nil :body edge}]]
      (is (nil? (loops/view (replace-body barrier)))))
    (let [bad (assoc-in node [:inits 0 :body :then :args] [])]
      (is (= :backedge-arity (check-of #(loops/inspect! bad))))
      (is (nil? (unbox/loop-kinds bad {}))))
    (is (some? (loops/view (replace-body {:op :quote :datum {:op :local :name self}}))))
    ;; Structural recognition is not purity evidence. Consumers must still
    ;; decline host effects and unknown layouts independently.
    (let [effectful (replace-body {:op :perform :target nil :name :host/call :args []})]
      (is (some? (loops/view effectful)))
      (is (empty? (unbox/loop-kinds effectful {})))
      (is (thrown? clojure.lang.ExceptionInfo (scalar/analyze effectful {} {} nil))))))

(deftest invalid-transfer-interfaces-decline-before-emission
  (doseq [[dest args] [[['a 'b] [1]] [['a 'a] [1 2]] [[nil] [1]]]]
    (is (= :transfer-interface (check-of #(loops/transfer dest args))))))

(deftest transfer-checker-binds-numeric-representation-and-exact-commit-order
  (let [destinations ['a 'b] arguments [{:op :local :name 'b} {:op :quote :datum 1}]
        plan (loops/transfer destinations arguments)]
    (is (= 2 (:arity (loops/check-transfer! destinations arguments plan))))
    (doseq [bad [(assoc-in plan [:evaluations 1 :expression :datum] 1N)
                 (assoc-in plan [:evaluations 1 :temporary] 0)
                 (update plan :commits #(vec (reverse %)))
                 (update plan :evaluations pop)]]
      (is (thrown? clojure.lang.ExceptionInfo (loops/check-transfer! destinations arguments bad))))))

(defn observe [f]
  (try [:value (f)] (catch Throwable ex [:error (class ex) (.getMessage ex)])))

(deftest installed-scalar-loops-preserve-swaps-strides-exits-and-overflow
  (doseq [[form inputs]
          [[sample [[0] [1] [2] [5] [12]]]
           ['(fn [n] (loop [i 0 a 1 b 2]
                       (if (< i n) (if (> a 20) b (recur (+ i 2) b (+ a b))) a)))
            [[0] [1] [5] [12] [100]]]
           ['(fn [n] (loop [i 0 a 1 b 2]
                       (if (< i n) (recur (inc i) b a) (+ (* 10 a) b))))
            [[0] [1] [2] [11]]]
           ['(fn [n seed] (loop [i 0 a seed b 1]
                            (if (< i n) (recur (inc i) b (+ a b)) a)))
            [[0 Long/MAX_VALUE] [1 Long/MAX_VALUE] [2 4] [2 Long/MIN_VALUE]]]
           ['(fn [n] (loop [i n again true] (if again (recur (+ i 1) false) i)))
            [[0] [3] [Long/MAX_VALUE]]]
           ['(fn [n] (loop [i n a 0]
                       (if (> i 0) (recur (dec i) (+ a i))
                         (loop [j 0 s a] (if (< j n) (recur (inc j) (+ s j)) s)))))
            [[0] [1] [7]]]]]
    (let [source (d/eval-form w/empty-root (list 'code form))
          core (code/s->core (code/code-term source))
          closure (ev/run core) cache (stage/make-cache)
          candidate (staged/prepare w/empty-root source)]
      (staged/install! cache w/empty-root candidate)
      (doseq [args inputs]
        (is (= (observe #(ev/call-value closure args))
               (observe #(stage/with-cache cache (ev/call-value closure args)))) (pr-str [form args])))
      (is (= (count inputs) (:hits (stage/stats cache)))))))
