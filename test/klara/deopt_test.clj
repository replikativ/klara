(ns klara.deopt-test
  "S7: speculation points inside a body, frame states and deopt.

  Each speculative executable below is a residual written by hand, as a
  specializer would emit it: it performs an effect, then speculates on
  the value the effect returned. When the guard fails, T0 rebuilds the
  generic code's state at the corresponding point from the frame state
  and resumes there. Gate R3 extended to mid-body guards: the same
  result and the same effect trace (each effect exactly once) with no
  cache, with the cache, and after deleting it."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.authority :as a]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]
            [klara.stage :as s]))

(def definitions
  '[;; generic code
    (def step (fn [h x]
                (let [y (perform h :get x)]
                  (+ 1 (if (integer? y) (* y 2) (perform h :fallback y))))))
    (def sum-gets (fn [h n]
                    (loop [i 0 acc 0]
                      (if (< i n) (recur (inc i) (+ acc (perform h :get i))) acc))))
    (def scaled (fn [h x]
                  (handle [a {:ask (fn [k] (k 10))}]
                    (let [y (perform h :get x)]
                      (if (integer? y) (* y (perform a :ask)) (+ (perform a :ask) 0.5))))))
    (def pay (fn [h e x]
               (let [_ (spend! e 1/4)
                     y (perform h :get x)]
                 (if (integer? y) y (* 2 y)))))
    ;; residuals: the effect, then a guard on its result
    (def step-fast (fn [h x]
                     (let [y (perform h :get x)]
                       (speculate (integer? y) (+ 1 (* y 2)) 0 [h x y]))))
    (def sum-gets-fast (fn [h n]
                         (loop [i 0 acc 0]
                           (if (< i n)
                             (let [y (perform h :get i)]
                               (speculate (integer? y) (recur (inc i) (+ acc y)) 0 [h n i acc y (inc i)]))
                             acc))))
    ;; the handler `a` is erased: :ask is answered inline
    (def scaled-fast (fn [h x]
                       (let [y (perform h :get x)]
                         (speculate (integer? y) (* y 10) 0 [h x y]))))
    (def pay-fast (fn [h e x]
                    (let [_ (spend! e 1/4)
                          y (perform h :get x)]
                      (speculate (integer? y) y 0 [h e x _ y]))))])

;; Frame states, against the expanded generic terms (paths from the fn term).
(def frame-states
  {'step
   ;; inside (+ 1 [if ..]): locals [h x y]; the + has evaluated 1
   [{:site :y-long :at [:eval [:body :body :args 1]]
     :env [[:live 0] [:live 1] [:live 2]]
     :kont [{:tag :list :path [:body :body] :env 3 :vals [[:const 1]]}]}]
   'sum-gets
   ;; (perform h :get i) has returned y into (+ acc _) inside (loop-fn (inc i) _);
   ;; locals [h n 0 0 loop-fn i acc]; loop-fn is rebuilt (an elided closure)
   [{:site :get-long :at [:ret [:live 4]]
     :env [[:live 0] [:live 1] [:const 0] [:const 0] [:letrec [:body :body :body] 0]
           [:live 2] [:live 3]]
     :kont [{:tag :list :path [:body :body :body :inits 0 :body :then] :env 7
             :vals [[:local 4] [:live 5]]}
            {:tag :list :path [:body :body :body :inits 0 :body :then :args 1] :env 7
             :vals [[:live 3]]}]}]
   'scaled
   ;; inside the handle body: locals [h x a y]; the handler frame and its
   ;; instance are rebuilt (pending handler context the residual erased)
   [{:site :y-long :at [:eval [:body :body :body]]
     :env [[:live 0] [:live 1] [:instance :lexical] [:live 2]]
     :kont [{:tag :handle :path [:body] :env 2 :instance [:local 2]
             :clauses {:ask [:closure [:body :clauses :ask]]}}]}]
   'pay
   ;; after the spend: locals [h e x _ y]; the evidence is a live value
   [{:site :y-long :at [:eval [:body :body :body]]
     :env [[:live 0] [:live 1] [:live 2] [:live 3] [:live 4]]}]})

(defn- world []
  (let [wo (w/make-world)]
    (doseq [df definitions] (d/define! wo df))
    wo))

(defn- speculative [root sym]
  (let [f (d/lookup root sym)]
    (s/speculative f (d/lookup root (symbol (str sym "-fast"))) (frame-states sym)
                   (into #{[:captures []]} (s/world-guards (ev/closure-term f) root))
                   {:author :deopt-test})))

(defn- cache-with [root & syms]
  (let [c (s/make-cache)]
    (doseq [sym syms] (s/install! c (speculative root sym)))
    c))

(def handler-src
  ;; :get answers x, except that 3, 500 and 7 answer a non-integer; every
  ;; operation is logged once per performance
  '(fn [trace prog]
     (handle [h {:get (fn [x k] (do (swap! trace conj [:get x])
                                    (k (if (contains? #{3 7 500} x) (+ x 0.5) x))))
                 :fallback (fn [y k] (do (swap! trace conj [:fallback y]) (k (* 10 y))))}]
       (prog h))))

(defn- traced
  "[result trace] of (prog h) under the logging handler."
  [root prog-src]
  (let [trace (atom [])
        run (d/eval-form root handler-src)
        v (run trace (d/eval-form root prog-src))]
    [v @trace]))

(def programs
  '[(fn [h] (step h 4))
    (fn [h] (step h 3))
    (fn [h] [(step h 1) (step h 3) (step h 5)])
    (fn [h] (sum-gets h 10))
    (fn [h] (sum-gets h 1000))
    (fn [h] (scaled h 4))
    (fn [h] (scaled h 7))])

(deftest r3-mid-body-guards
  (let [root (w/snapshot (world))
        generic (mapv #(traced root %) programs)
        cache (cache-with root 'step 'sum-gets 'scaled)
        cached (s/with-cache cache (mapv #(traced root %) programs))]
    (is (= generic cached) "same results and same effect traces")
    (is (pos? (:hits (s/stats cache))))
    (is (= 5 (:deopts (s/stats cache))) "(step h 3) twice, each sum-gets once (at i = 3), (scaled h 7)")
    (testing "each effect exactly once"
      (let [[[v tr]] (s/with-cache cache [(traced root '(fn [h] (step h 3)))])]
        (is (= 36.0 v))
        (is (= [[:get 3] [:fallback 3.5]] tr) "the :get before the guard is not repeated")))
    (s/clear! cache)
    (is (= generic (s/with-cache cache (mapv #(traced root %) programs))) "after deletion")))

(deftest deopt-in-the-middle-of-a-loop
  (let [root (w/snapshot (world))
        cache (cache-with root 'sum-gets)
        [v tr] (s/with-cache cache (traced root '(fn [h] (sum-gets h 1000))))]
    (is (== (+ (- (reduce + (range 1000)) 3 7 500) 3.5 7.5 500.5) v))
    (is (= (mapv #(vector :get %) (range 1000)) tr) "every iteration's :get exactly once, in order")
    (is (= {:hits 1 :deopts 1} (select-keys (s/stats cache) [:hits :deopts]))
        "one entry; the first failure (i = 3) leaves for generic T0, which finishes the loop")
    (testing "the speculative loop runs in constant space while its guard holds"
      (let [cache (cache-with root 'sum-gets)
            run (d/eval-form root '(fn [] (handle [h {:get (fn [x k] (k x))}] (sum-gets h 100000))))]
        (is (= (reduce + (range 100000)) (s/with-cache cache (run))))
        (is (zero? (:deopts (s/stats cache))))))))

(deftest pending-handler-context
  (let [root (w/snapshot (world))
        cache (cache-with root 'scaled)]
    (is (= [40 [[:get 4]]] (s/with-cache cache (traced root '(fn [h] (scaled h 4))))))
    (is (= [10.5 [[:get 7]]] (s/with-cache cache (traced root '(fn [h] (scaled h 7)))))
        "after deopt, (perform a :ask) finds the rebuilt handler frame")
    (is (= 1 (:deopts (s/stats cache))))))

(deftest authority-holding-frame-state
  (let [root (w/snapshot (world))
        prog (d/eval-form root
                          '(fn [x] (let [e (evidence 1)]
                                     [(handle [h {:get (fn [x k] (k (if (= x 3) 1.5 x)))}]
                                        (pay h e x))
                                      (remaining e)])))
        run (fn [x] (binding [a/*store* (a/new-store)] (prog x)))
        cache (cache-with root 'pay)]
    (is (= [4 3/4] (run 4) (s/with-cache cache (run 4))))
    (is (= [3.0 3/4] (run 3)))
    (is (= [3.0 3/4] (s/with-cache cache (run 3)))
        "deopt resumes after the spend: the evidence is spent once (replay from entry would leave 1/2)")
    (is (= 1 (:deopts (s/stats cache))))
    (testing "a resource consumed before the guard is consumed once"
      (let [wo (world)
            _ (d/define! wo '(def take1 (fn [r h] (let [p (consume! r) y (perform h :get p)]
                                                    (if (integer? y) y (str y))))))
            _ (d/define! wo '(def take1-fast (fn [r h] (let [p (consume! r) y (perform h :get p)]
                                                         (speculate (integer? y) y 0 [r h p y])))))
            root (w/snapshot wo)
            f (d/lookup root 'take1)
            exe (s/speculative f (d/lookup root 'take1-fast)
                               [{:site :y :at [:eval [:body :body :body]]
                                 :env [[:live 0] [:live 1] [:live 2] [:live 3]]}]
                               (into #{[:captures []]} (s/world-guards (ev/closure-term f) root))
                               {:author :deopt-test})
            cache (doto (s/make-cache) (s/install! exe))
            prog (d/eval-form root '(fn [] (let [r (resource 7)]
                                             [(handle [h {:get (fn [p k] (k (/ p 2)))}] (take1 r h))
                                              (status r)])))]
        (binding [a/*store* (a/new-store)]
          (is (= ["7/2" {:kind :resource :status :settled :operation :consume}]
                 (s/with-cache cache (prog)))))
        (is (= 1 (:deopts (s/stats cache))))))
    (testing "an authority constant in a frame state is refused at install"
      (let [r (binding [a/*store* (a/new-store)] (d/eval-form root '(resource 1)))
            f (d/lookup root 'pay)
            bad (s/speculative f (d/lookup root 'pay-fast)
                               [(assoc-in (first (frame-states 'pay)) [:env 1] [:const {:r r}])]
                               (into #{[:captures []]} (s/world-guards (ev/closure-term f) root))
                               {:author :deopt-test})]
        (is (= :bad-frame-state
               (try (s/install! (s/make-cache) bad) nil
                    (catch Exception e (:reason (ex-data e))))))))
    (testing "deopt inside a fork branch opened by the caller settles normally"
      (binding [a/*store* (a/new-store)]
        (let [prog (d/eval-form root
                                '(fn [] (let [e (evidence 1)
                                              v (fork [b (handle [h {:get (fn [x k] (k (+ x 0.5)))}] (pay h e 3))]
                                                  (adopt! b)
                                                  (:value b))]
                                          [v (remaining e)])))
              [v rem] (s/with-cache cache (prog))]
          (is (= 7.0 v))
          (is (= 3/4 rem) "the adopted branch's single spend is committed")
          (is (= 2 (:deopts (s/stats cache))) "the deopt did happen inside the branch"))))))

(deftest deopt-refuses-to-drop-a-fork
  (let [wo (world)
        _ (d/define! wo '(def forked (fn [h] (fork [b (perform h :get 3)] (:value b)))))
        _ (d/define! wo '(def forked-fast (fn [h] (fork [b (let [y (perform h :get 3)]
                                                             (speculate (integer? y) y 0 [h y]))]
                                                    (:value b)))))
        root (w/snapshot wo)
        f (d/lookup root 'forked)
        exe (s/speculative f (d/lookup root 'forked-fast)
                           [{:site :y :at [:ret [:live 1]] :env [[:live 0]]}]
                           (into #{[:captures []]} (s/world-guards (ev/closure-term f) root))
                           {:author :deopt-test})
        cache (doto (s/make-cache) (s/install! exe))]
    (is (re-find #"deopt! across a branch frame"
                 (try (s/with-cache cache (traced root '(fn [h] (forked h)))) ""
                      (catch Exception e (ex-message e))))
        "a branch frame of the speculative code has no generic counterpart to rebuild")))

(deftest host-executable-mid-body-deopt
  (let [wo (world)
        _ (d/define! wo '(def total (fn [xs] (let [t (reduce + 0 xs)] (if (< t 100) (* t 2) (str t))))))
        root (w/snapshot wo)
        f (d/lookup root 'total)
        work (atom 0)
        exe (s/speculative f (fn [xs] (let [t (do (swap! work inc) (reduce + 0 xs))]
                                        (if (< t 100) (* t 2) (s/deopt! 0 [xs t]))))
                           [{:site :t-small :at [:eval [:body :body]] :env [[:live 0] [:live 1]]}]
                           #{[:captures []] [:arg 0 :vector]}
                           {:author :deopt-test})
        cache (doto (s/make-cache) (s/install! exe))]
    (s/with-cache cache
      (is (= 20 (f [1 2 3 4])))
      (is (= "150" (f [50 100]))))
    (is (= 2 @work) "the host work before the guard ran once per call; generic resumed after it")
    (is (= {:hits 2 :deopts 1} (select-keys (s/stats cache) [:hits :deopts])))))

(deftest frame-states-are-checked-at-install
  (let [root (w/snapshot (world))
        good (speculative root 'step)
        reason (fn [exe] (try (s/install! (s/make-cache) exe) :installed
                              (catch Exception e (:reason (ex-data e)))))
        recertify (fn [exe] (s/speculative (d/lookup root 'step) (:klara exe) (:frame-states exe)
                                           (:guards exe) {:author :deopt-test}))]
    (is (= :installed (reason good)))
    (is (= :frame-state-mismatch (reason (assoc-in good [:frame-states 0 :site] :other)))
        "frame states are part of the certificate")
    (is (= :bad-frame-state (reason (recertify (update-in good [:frame-states 0 :env] pop))))
        "the environment shape must match the generic scope at the position")
    (is (= :bad-frame-state (reason (recertify (assoc-in good [:frame-states 0 :at] [:eval [:body :nope]])))))
    (is (= :bad-frame-state (reason (recertify (assoc-in good [:frame-states 0 :kont 0 :env] 2)))))))

(deftest feedback-drives-the-speculation-decision
  (let [root (w/snapshot (world))
        f (d/lookup root 'step)
        site [(:code-id (speculative root 'step)) :y-long]
        cache (s/make-cache)
        fb (s/cache-feedback cache)
        specialize! (fn []
                      (s/clear! cache)
                      (s/install! cache (if (s/speculate? fb site)
                                          (speculative root 'step)
                                          (s/residual f root))))
        prog (d/eval-form root '(fn [trace xs] (handle [h {:get (fn [x k] (do (swap! trace conj x) (k (if (odd? x) (+ x 0.5) x))))
                                                         :fallback (fn [y k] (k y))}]
                                                (loop [xs xs acc []]
                                                  (if (empty? xs) acc (recur (rest xs) (conj acc (step h (first xs)))))))))
        go (fn [xs] (let [t (atom [])] [(s/with-cache cache (prog t xs)) @t]))
        generic (fn [xs] (let [t (atom [])] [(prog t xs) @t]))]
    (specialize!)
    (is (= (generic [2 4 1]) (go [2 4 1])))
    (is (= 1 (s/observed fb site :deopt)))
    (specialize!)
    (is (:frame-states (first (s/executables cache))) "one deopt: still speculating")
    (is (= (generic [3 5 6]) (go [3 5 6])))
    (is (= 3 (s/observed fb site :deopt)))
    (specialize!)
    (is (nil? (:frame-states (first (s/executables cache)))) "three deopts: the site is poisoned")
    (is (= (generic [7 9]) (go [7 9])))
    (is (= 3 (s/observed fb site :deopt)) "the non-speculative residual never deopts")
    (testing "counters are monotone and capped; snapshots join by max"
      (let [fb (s/make-feedback)]
        (dotimes [_ (+ 10 s/feedback-cap)] (s/observe! fb [:c :s] :deopt))
        (is (= s/feedback-cap (s/observed fb [:c :s] :deopt)))
        (is (= {[[:c :s] :deopt] s/feedback-cap [[:c :t] :deopt] 2}
               (s/join-feedback (s/feedback fb) {[[:c :s] :deopt] 5 [[:c :t] :deopt] 2})))))))
