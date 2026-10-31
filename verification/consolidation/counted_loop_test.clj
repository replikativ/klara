(ns consolidation.counted-loop-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.counted-loop :as loop] [consolidation.counted-loop-model :as model]
            [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k] [klara.core :as c] [klara.eval :as ev]
            [klara.expand :as x] [klara.world :as w] [klara.defs :as defs]
            [interpreter.bridge-checks :as bridge]))

(def rhses [(c/prim '+ (c/local 0) (c/local 1))
            (c/prim '+ (c/local 0) (c/prim '* (c/local 1) (c/local 1)))
            (c/let1 (c/prim '+ (c/local 1) (c/quote* 1))
                    (c/prim '+ (c/local 1) (c/local 0)))])

(deftest kernel-checked-counted-loop-composition
  (doseq [name model/theorem-names
          :let [en @model/proof-state d (env/lookup en (nm/from-string name))]]
    (is (env/verifies? en (env/ci-type d) (env/ci-value d)))
    (is (not (contains? (k/constants-of (env/ci-value d)) name))))
  (doseq [rhs rhses :let [source (loop/source rhs) receipt (loop/certify source)]]
    (is (loop/verify? source receipt))
    (is (not (loop/verify? source (assoc receipt :source-id "stale"))))
    (is (not (loop/verify? source (assoc receipt :proof (:goal receipt)))))
    (is (not (loop/verify? source (assoc-in receipt [:acc :block :result] 0))))))

(defn- next-condition [state loop-body]
  (loop [state (ev/step-state state) fuel 2000]
    (assert (pos? fuel) "no next reference backedge")
    (if (and (= :eval (first state)) (= loop-body (second state))) state
      (recur (ev/step-state state) (dec fuel)))))

(deftest every-backedge-matches-reference-and-recovers
  (doseq [rhs rhses tier [:generic :primitive] n [0 1 4 8]
          :let [artifact (loop/prepare (loop/source rhs))
                expected ((ev/run (:source artifact)) n)]]
    (loop [snapshot (loop/start artifact n)
           reference (loop/reference-state artifact (loop/start artifact n))]
      (is (= (bridge/signature reference w/empty-root)
             (bridge/signature (loop/reference-state artifact snapshot) w/empty-root)))
      (is (= expected (loop/resume-reference artifact snapshot)))
      (let [{:keys [status] next-snapshot :snapshot} (loop/run-chunk artifact snapshot 1 tier)]
        (if (= (:index snapshot) n)
          (do (is (= :done status)) (is (= expected (:acc next-snapshot))))
          (do (is (= (inc (:index snapshot)) (:index next-snapshot)))
              (recur next-snapshot (next-condition reference (:loop-body artifact)))))))))

(deftest zero-budget-composition-and-simultaneous-old-state-updates
  (let [artifact (loop/prepare (loop/source (first rhses)))
        initial (loop/start artifact 10)
        zero (loop/run-chunk artifact initial 0 :primitive)
        one (loop/run-chunk artifact initial 1 :primitive)
        a (loop/run-chunk artifact (:snapshot one) 3 :generic)
        b (loop/run-chunk artifact initial 4 :primitive)]
    (is (= {:status :paused :snapshot initial} zero))
    ;; Sequentially updating i before evaluating s+i would produce 1 here.
    (is (= [1 0] ((juxt :index :acc) (:snapshot one))))
    (is (= (:snapshot a) (:snapshot b)))
    (is (= 45 (loop/invoke artifact 10 :generic) (loop/invoke artifact 10 :primitive)))
    ;; Snapshots are immutable; running either branch cannot alter initial.
    (is (= [0 0] ((juxt :index :acc) initial)))
    (is (= :done (:status (loop/run-chunk artifact (loop/start artifact 0) 0 :generic))))))

(deftest overflow-inputs-protocol-and-stale-contexts-decline
  (let [artifact (loop/prepare (loop/source (c/prim '+ (c/local 0) (c/quote* 1)) Long/MAX_VALUE))
        snapshot (loop/start artifact 1)]
    (doseq [tier [:generic :primitive]]
      (is (thrown? ArithmeticException (loop/run-chunk artifact snapshot 1 tier))))
    (is (thrown? ArithmeticException (loop/resume-reference artifact snapshot)))
    (is (= Long/MAX_VALUE (:acc snapshot))))
  (let [source (loop/source (first rhses)) artifact (loop/prepare source) snapshot (loop/start artifact 5)]
    (doseq [bad [-1 1N 1.0 (atom 0)]]
      (is (thrown? clojure.lang.ExceptionInfo (loop/start artifact bad))))
    (doseq [bad [(assoc snapshot :source-id "wrong") (assoc snapshot :index 6)
                 (assoc snapshot :acc -1) (assoc snapshot :basis (assoc w/empty-root :version 99))]]
      (is (thrown? clojure.lang.ExceptionInfo (loop/run-chunk artifact bad 1 :primitive))))
    (is (thrown? clojure.lang.ExceptionInfo (loop/run-chunk artifact snapshot -1 :generic)))
    (with-redefs [c/prims (assoc c/prims '+ (fn [& _] :wrong))]
      (is (thrown? clojure.lang.ExceptionInfo (loop/run-chunk artifact snapshot 1 :primitive))))
    (doseq [bad [(assoc-in source [:body :body :body :inits 0 :body :then :args 0] (c/local 1))
                 (assoc-in source [:body :body :body :inits 0 :body :test :name] '<=)
                 (assoc-in source [:body :body :body :inits 0 :body :then :args 1] (c/local 5))]]
      (is (thrown? clojure.lang.ExceptionInfo (loop/prepare bad))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (loop/prepare (x/expand-expr '(fn [n] (println n)) w/empty-root))))))

(deftest snapshots-retain-the-pinned-world
  (let [world (w/make-world) _ (defs/define! world '(def marker :old)) basis (w/snapshot world)
        artifact (loop/prepare (loop/source (first rhses)) basis)
        snapshot (:snapshot (loop/run-chunk artifact (loop/start artifact 7) 3 :primitive))]
    (defs/define! world '(def marker :new))
    (is (identical? basis (:basis snapshot)))
    (is (identical? basis (:basis (nth (loop/reference-state artifact snapshot) 2))))
    (is (= 21 (loop/resume-reference artifact snapshot)))))

(deftest chunk-quota-is-lifted-without-overflow-or-extra-iterations
  (let [artifact (loop/prepare (loop/source (c/local 0)))]
    (doseq [tier [:generic :primitive]]
      (let [near-end (assoc (loop/start artifact Long/MAX_VALUE) :index (dec Long/MAX_VALUE))
            result (loop/run-chunk artifact near-end Long/MAX_VALUE tier)]
        (is (= :done (:status result)))
        (is (= Long/MAX_VALUE (get-in result [:snapshot :index])))
        (is (= 0 (loop/resume-reference artifact near-end))))
      (doseq [n [0 1 7] fuel [0 1 3 Long/MAX_VALUE]]
        (let [result (loop/run-chunk artifact (loop/start artifact n) fuel tier)
              expected (min n fuel)]
          (is (= expected (get-in result [:snapshot :index])))
          (is (= (if (= expected n) :done :paused) (:status result))))))))
