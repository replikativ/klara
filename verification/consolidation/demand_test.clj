(ns consolidation.demand-test
  (:require [clojure.test :refer [deftest is]] [clojure.java.io :as io]
            [consolidation.demand :as demand] [consolidation.demand-model :as model]
            [ansatz.kernel.env :as env]
            [klara.code :as code] [klara.core :as c] [klara.eval :as ev]
            [klara.authority :as authority] [klara.defs :as d]
            [klara.compile.staged :as staged] [klara.compile.strict-fold :as fold]
            [klara.infer-affine-test :as base] [klara.stage :as stage] [klara.world :as w]))

(defn as-code [term] (code/->code (code/core->s term)))
(defn request [polynomial prefix domain kind]
  {:source (as-code (demand/source-term (base/term polynomial) prefix kind))
   :target (as-code (demand/target-term (base/term polynomial) prefix)) :domain domain})
(defn call [source xs] (base/call source [xs]))

(deftest bounded-total-map-prefixes-compose-through-the-shared-native-backend
  (let [polynomial (base/source '(fn [x] (+ 1 (* x (+ 2 (* x 3))))))
        domain {:max-count 64 :max-x 10} random (java.util.Random. 3001)]
    (doseq [prefix [0 1 3 64] kind ['map 'mapv]]
      (let [r (request polynomial prefix domain kind) cache (stage/make-cache)
            candidate (demand/prepare w/empty-root r)]
        (is (= :installed (:status (staged/install! cache w/empty-root candidate))))
        (dotimes [_ 12]
          (let [xs (vec (repeatedly (.nextInt random 12) #(long (.nextInt random 11))))
                expected (reduce + 0 (take prefix (map #(+ 1 (* % (+ 2 (* % 3)))) xs)))]
            (is (= expected (call (:source r) xs)))
            (is (= expected (call (:target r) xs)))
            (is (= expected (stage/with-cache cache (call (:source r) xs))))))
        (is (pos? (:hits (stage/stats cache))))))))

(deftest demand-does-not-license-suppressing-chunk-errors-or-forcing-a-safe-prefixs-tail
  (let [polynomial (base/source '(fn [x] (* x x))) domain {:max-count 40 :max-x Long/MAX_VALUE}
        r (request polynomial 1 domain 'map)
        in-chunk (assoc (vec (repeat 40 0)) 5 Long/MAX_VALUE)
        after-chunk (assoc (vec (repeat 40 0)) 35 Long/MAX_VALUE)
        eager (as-code (demand/source-term (base/term polynomial) 1 'mapv))]
    ;; Same supported arithmetic syntax; rejection is actual totality/range failure.
    (is (= :overflow (try (demand/prepare w/empty-root r) :accepted
                         (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))
    (is (= :error (first (base/observe #(call (:source r) in-chunk)))))
    (is (= 0 (call (:target r) in-chunk)))
    (is (= 0 (call (:source r) after-chunk)))
    (is (= :error (first (base/observe #(call eager after-chunk)))))
    (is (= 0 (call (:target r) after-chunk)))))

(deftest exact-endpoints-domain-and-kernel-evidence-are-required
  (let [p (base/source '(fn [x] (+ x 1))) r (request p 3 {:max-count 8 :max-x 10} 'map)
        cache (stage/make-cache)]
    (staged/install! cache w/empty-root (demand/prepare w/empty-root r))
    (doseq [xs [[11] [-1] [1.5] [1N] '(1 2 3)]]
      (is (= (base/observe #(call (:source r) xs))
             (stage/with-cache cache (base/observe #(call (:source r) xs))))))
    (is (= 5 (:fallbacks (stage/stats cache))))
    (let [exe (first (stage/executables cache))]
      (is (= :invalid-demand-prefix (stage/check-certificate (assoc-in exe [:witness :proof] (get-in exe [:witness :goal])))))
      (is (= :invalid-demand-prefix (stage/check-certificate (assoc-in exe [:witness :goal-sha256] "wrong")))))
    (let [bad (assoc r :target (as-code (demand/target-term (base/term p) 4)))]
      (is (= :endpoint-mismatch (try (demand/prepare w/empty-root bad) :accepted
                                    (catch clojure.lang.ExceptionInfo ex (:check (ex-data ex)))))))
    (let [big-source (as-code (assoc-in (base/term (:source r)) [:body :args 2 :datum] 0N))]
      (is (= :source-interface (try (demand/prepare w/empty-root (assoc r :source big-source)) :accepted
                                   (catch clojure.lang.ExceptionInfo ex (:check (ex-data ex)))))))))

;; A bounded operational observer, independent of ansatz's generated JVM code.
;; :pending means observation budget exhausted; it is not a source exception.
(defn observe [fuel amount plan]
  (loop [fuel fuel amount amount plan plan values []]
    (cond (zero? amount) {:status :ok :values values}
          (zero? fuel) {:status :pending :values values}
          :else (case (first plan)
                  :done {:status :ok :values values}
                  :fault {:status :fault :values values :category (second plan)}
                  :spin (recur (dec fuel) amount plan values)
                  :yield (recur (dec fuel) (dec amount) (nth plan 2) (conj values (second plan)))))))

(deftest zero-and-prefix-demand-do-not-force-unknown-tails
  (doseq [fuel (range 1 8) tail [[:fault 0] [:spin]]]
    (is (= {:status :ok :values [7]} (observe fuel 1 [:yield 7 tail]))))
  (is (= {:status :ok :values []} (observe 0 0 [:spin])))
  (is (= {:status :fault :values [7] :category 0} (observe 2 2 [:yield 7 [:fault 0]])))
  (doseq [fuel (range 12)]
    (is (= {:status :pending :values [7]} (observe (inc fuel) 2 [:yield 7 [:spin]]))))
  (let [checked (demand/check-request (request (base/source '(fn [x] (+ x 1))) 1 {:max-count 2 :max-x 10} 'map))]
    (is (env/verifies? @model/proof-state (get-in checked [:witness :goal]) (get-in checked [:witness :proof])))))

(defn example-world []
  (let [world (w/make-world)]
    (with-open [reader (java.io.PushbackReader. (io/reader "examples/staging/14-demand-and-await.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} reader)))]
        (d/define! world form))) world))

(deftest actual-staged-prefix-preparation-and-t0-one-shot-suspension
  (let [world (example-world) old (w/snapshot world) cache (stage/make-cache) store (authority/new-store)]
    (binding [authority/*store* store]
      (stage/with-cache cache
        (is (= :installed (:status (d/eval-form old '(refine-prefix prefix-request)))))
        (is (= 9 (d/eval-form old '(prefix-statistic [1 2 3 4]))))
        (d/define! world '(def saved-task (start-prefix-task [1 2 3 4])))
        (let [task (d/lookup (w/snapshot world) 'saved-task)]
          (is (= :suspended (:status task)))
          (is (= {:before 9} (:request task)))
          (d/define! world '(def calibration 100))
          (let [new (w/snapshot world) resume (fn [] (d/eval-form new '(resume-prefix-task saved-task 5)))]
            (is (= {:value 33 :calibration 10} (resume)))
            (is (= :settled (:status (authority/state (:lease task)))))
            (is (re-find #"captured a resource|settled" (try (resume) "unexpected" (catch Throwable ex (ex-message ex)))))))))))

(deftest cancellation-consults-live-permissions-and-owned-capture-still-rejects
  (let [world (example-world) root (w/snapshot world) store (authority/new-store)]
    (binding [authority/*store* store]
      (d/define! world '(def saved-task (start-prefix-task [1 2 3])))
      (let [root (w/snapshot world)]
        (is (= :resume-once (d/eval-form root '(cancel-prefix-task saved-task))))
        (is (= :settled (:status (authority/state (:lease (d/lookup root 'saved-task))))))
        (is (re-find #"settled" (try (d/eval-form root '(resume-prefix-task saved-task 5))
                                     "unexpected" (catch Throwable ex (ex-message ex)))))))
    (binding [authority/*store* (authority/new-store)]
      (is (re-find #"owned|full share|write share"
                   (try (d/eval-form root '(let [cell (perform :own/alloc [0])]
                                            (handle [h {:await (fn [k] {:resume k})}]
                                              (do (perform h :await) (perform :own/freeze cell)))))
                        "unexpected" (catch Throwable ex (ex-message ex))))))))

(deftest zero-element-demand-does-not-erase-producer-construction
  (let [world (example-world) cache (stage/make-cache)]
    (d/define! world '(def zero-code (prefix-builder shift-scalar-code 0)))
    (d/define! world '(def zero-request {:source (:source zero-code) :target (:target zero-code)
                                       :domain {:max-count 64 :max-x 10}}))
    (d/define! world '(def zero-statistic (run (:source zero-code))))
    (let [root (w/snapshot world)]
      (staged/install! cache root (demand/prepare root (d/lookup root 'zero-request)))
      (is (= 0 (stage/with-cache cache (d/eval-form root '(zero-statistic [1 2 3])))))
      (is (= 99 (stage/with-cache cache
                  (d/eval-form root '(handle :dynamic {:host/call (fn [& args] 99)}
                                      (zero-statistic [1 2 3]))))))
      (is (= 1 (:fallbacks (stage/stats cache)))))))
