(ns adaptive-affine.calibration-demo-test
  (:require [clojure.test :refer [deftest is]]
            [adaptive-affine.calibration-demo :as demo]
            [klara.authority :as authority] [klara.code :as code]
            [klara.compile.staged :as staged]
            [klara.defs :as defs] [klara.world :as world]))

(deftest online-learning-changes-the-prediction-without-changing-the-answer
  (let [{:keys [steps model compiled-kernels]} (demo/example)]
    (is (= [:normal :normal :normal :alert] (mapv :predicted steps)))
    (is (= [:normal :alert :alert :alert] (mapv :observed steps)))
    (is (= [:reuse :fallback :fallback :reuse] (mapv :path steps)))
    (is (= [21 40 40 40] (mapv :value steps)))
    (is (= {:normal 1 :alert 3} model))
    (is (= 2 compiled-kernels))))

(deftest specialized-code-and-speculation-agree-with-the-reference
  (let [s (demo/session) root (:basis s) reference (defs/lookup root 'reference-calibration)
        builder (defs/lookup root 'calibration-code)]
    (try
      (doseq [model [{} {:normal 10} {:alert 10}]
              readings [[] [10 20] [101] [10 120 30]]
              x [0 10 1000]]
        (is (= (reference readings x) (:value (demo/step! s model readings x)))))
      (is (= '(fn [x_1] (+ (* x_1 2) 1)) (code/code->form (builder :normal))))
      (is (= '(fn [x_1] (+ (* x_1 3) 10)) (code/code->form (builder :alert))))
      (is (= 2 (count @(:compiled s))) "both generated CodeIds reuse their kernels")
      (is (empty? @(:jobs s)))
      (is (identical? root (world/snapshot (:world s))))
      ;; The wrong alert branch overflows. The real normal branch succeeds.
      (let [x (quot Long/MAX_VALUE 3)
            result (demo/step! s {:alert 1} [] x)]
        (is (= :fallback (:path result)))
        (is (= (reference [] x) (:value result))))
      (finally (demo/close! s)))))

(deftest unavailable-compilation-falls-back-and-still-trains
  (let [s (demo/session)]
    (try
      (with-redefs [staged/prepare (fn [_ _] (throw (ex-info "backend unavailable" {})))]
        (let [result (demo/step! s {} [10] 10)]
          (is (= :fallback (:path result)))
          (is (= 21 (:value result)))
          (is (= {:normal 1} (:model result)))
          (is (empty? @(:compiled s)))))
      (finally (demo/close! s)))))

(deftest host-service-rejects-effects-stale-bases-and-reused-tickets
  (let [s (demo/session) root (:basis s)
        builder (defs/lookup root 'calibration-code)]
    (try
      (binding [demo/*service* s authority/*store* (authority/new-store)]
        (let [bad (defs/eval-form root '(code (fn [x] (perform :stage/should-not-run x))))]
          (is (thrown? Exception (demo/start! bad 10 root)))
          (is (empty? @(:jobs s)))
          (is (empty? @(:compiled s))))
        (let [ticket (demo/start! (builder :normal) 10 root)]
          (is (thrown? Exception (demo/await! ticket (assoc root :version -1))))
          (is (= {:status :ok :value 21} (demo/await! ticket root)))
          (is (thrown? Exception (demo/await! ticket root)))))
      (finally (demo/close! s)))))
