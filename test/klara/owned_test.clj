(ns klara.owned-test
  "Store-level RFC 0005 tests. Surface/effect/checker integration is separate."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.authority :as a]))

(defn- op [name & args] (a/op! name args []))
(defn- mass []
  (reduce + 0 (for [s (vals (:tokens @a/*store*))
                    :when (and (= :owned (:kind s)) (#{:open :advancing} (:status s)))]
                (get-in s [:payload :share]))))
(defn- frames [g i] [{:tag :branch :ctx (a/group-ctx g i)}])

(deftest owned-lifecycle
  (binding [a/*store* (a/new-store)]
    (let [v [1 2] t (op :own/alloc v)]
      (is (= v (op :own/read t)))
      (is (= 1 (mass)))
      (is (= t (op :own/update t conj 3)))
      (is (= [1 2] v) "the old persistent value remains valid")
      (is (= [1 2 3] (op :own/read t)))
      (is (= 2 (:gen (a/state t))))
      (let [u (op :own/move t)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled \(move\)" (op :own/read t)))
        (is (= 1 (mass)))
        (is (= [1 2 3] (op :own/freeze u)))
        (is (zero? (mass)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/freeze u)))))
    (let [t (op :own/alloc :drop)]
      (is (nil? (op :own/drop t)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/drop t)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/update t identity))))))

(deftest owned-borrows
  (binding [a/*store* (a/new-store)]
    (let [t (op :own/alloc {:v 1}) b (a/borrow-owned! t 1/2 [])]
      (is (= 1 (mass)))
      (is (= {:v 1} (op :own/read t) (op :own/read b)))
      (doseq [name [:own/update :own/move :own/freeze :own/drop]
              token [t b]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share"
                              (op name token identity))))
      (let [c (a/borrow-owned! b 1/4 [])]
        (is (= 1 (mass)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"outstanding lends" (a/return-owned! b)))
        (a/return-owned! c)
        (is (= 1 (mass))))
      (a/return-owned! b)
      (is (= 1 (mass)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (a/return-owned! b)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/read b)))
      (op :own/update t assoc :v 2)
      (is (= {:v 2} (op :own/freeze t))))
    (let [t (op :own/alloc :v)]
      (doseq [q [0 -1 2 0.5 nil]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rational fraction" (a/borrow-owned! t q []))))
      (let [b (a/borrow-owned! t 1 [])]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"positive owned share" (op :own/read t)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share" (op :own/update b identity)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exceeds" (a/borrow-owned! t 1/2 [])))
        (a/return-owned! b))
      (is (thrown-with-msg? Exception #"body failed"
                            (a/with-owned-borrow t 1 [] (fn [_] (throw (Exception. "body failed"))))))
      (is (= 1 (get-in (a/state t) [:payload :share])))
      (is (= :v (op :own/freeze t))))))

(deftest owned-forks
  (binding [a/*store* (a/new-store)]
    (let [t (op :own/alloc [42])]
      (is (a/full-owned-held? []))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share"
                            (a/open-fork! {} 2 [])))
      (is (re-find #"full owned write share" (a/resume-blocker t)))
      (let [b (a/borrow-owned! t 1 [])]
        (is (not (a/full-owned-held? [])))
        (is (nil? (a/resume-blocker b)))
        (doseq [ws [[0 1] [0.1 0.9]]]
          (let [g (a/open-fork! {:shares {b ws}} 2 [])]
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"positive rational fractions"
                                  (a/op! :own/read [b] (frames g 0))))
            (a/close-group! g [] :abort)
            (is (= 1 (mass)))
            (is (= :open (:status (a/state b))))))
        (doseq [how [:exit :abort]]
          (let [g (a/open-fork! {} 3 [])]
            (doseq [i (range 3)]
              (is (= [42] (a/op! :own/read [b] (frames g i))))
              (is (= 1 (mass))))
            (is (= [1/3 1/3 1/3]
                   (mapv #(get-in (a/state %) [:payload :share])
                         (:children (first (vals (:leases @g)))))))
            (a/close-group! g [] how)
            (is (= 1 (mass)))
            (is (= [42] (op :own/read b)))))
        (let [g (a/open-fork! {} 2 [])
              outer (frames g 0)
              _ (a/op! :own/read [b] outer)
              h (a/open-fork! {} 2 outer)]
          (is (= [42] (a/op! :own/read [b] (into (frames h 1) outer))))
          (is (= 1 (mass)))
          (a/close-group! h outer :exit)
          (a/close-group! g [] :exit)
          (is (= 1 (mass))))
        (testing "loans escaped from a derived branch cannot duplicate shares on adoption"
          (let [g (a/open-fork! {} 2 [])
                fs (frames g 0)
                loan (a/borrow-owned! b 1/4 fs)]
            (is (= 1 (mass)))
            (a/adopt! (first (a/branches g [nil nil])))
            (a/close-group! g [] :exit)
            (is (= 1 (mass)))
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/read loan)))))
        (a/return-owned! b))
      (is (= [42] (op :own/freeze t))))))

(deftest owned-shot-and-contexts
  (binding [a/*store* (a/new-store)]
    (let [t (op :own/alloc :v)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share"
                            (a/op! :own/read [t] [(a/shot-frame)])))
      (a/with-owned-borrow
       t 1 []
       (fn [b]
         (let [frame (a/shot-frame) fs [frame]]
           (is (= :v (a/op! :own/read [b] fs)))
           (is (= 1 (mass)))
           (a/close-group! (:group (:ctx frame)) [] :exit)
           (is (= 1 (mass))))))
      (op :own/drop t))
    (testing "branch-minted cells survive adoption, die on discard, and reject sibling use"
      (doseq [adopt? [true false]]
        (let [g (a/open-fork! {} 2 [])
              t (a/op! :own/alloc [:branch] (frames g 0))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"belongs to a branch"
                                (a/op! :own/read [t] (frames g 1))))
          (when adopt? (a/adopt! (first (a/branches g [t nil]))))
          (a/close-group! g [] :exit)
          (if adopt?
            (is (= :branch (op :own/freeze t)))
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/read t)))))))))

(deftest owned-fork-loan-cleanup
  (binding [a/*store* (a/new-store)]
    (testing "adopting a fresh owned cell restores its full permission and closes escaped loans"
      (let [g (a/open-fork! {} 2 [])
            fs (frames g 0)
            t (a/op! :own/alloc [:fresh] fs)
            b (a/borrow-owned! t 1 fs)
            c (a/borrow-owned! b 1/2 fs)]
        (is (= 1 (mass)))
        (a/adopt! (first (a/branches g [t nil])))
        (a/close-group! g [] :exit)
        (is (= 1 (mass)))
        (doseq [loan [b c]]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled" (op :own/read loan))))
        (is (= :fresh (op :own/freeze t)))))
    (testing "the lender's remaining fraction also splits, with exact unequal weights"
      (let [t (op :own/alloc :partial) b (a/borrow-owned! t 1/4 [])
            g (a/open-fork! {:shares {t [1 2 3]}} 3 [])]
        (is (= :partial (a/op! :own/read [t] (frames g 0))))
        (is (= [1/8 1/4 3/8]
               (mapv #(get-in (a/state %) [:payload :share])
                     (:children (first (vals (:leases @g)))))))
        (is (= 1 (mass)))
        (a/close-group! g [] :exit)
        (is (= 1 (mass)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share" (op :own/update t identity)))
        (a/return-owned! b)
        (is (= :partial (op :own/freeze t)))))))

(deftest functional-update-lease
  (binding [a/*store* (a/new-store)]
    (let [t (op :own/alloc 3) calls (atom 0)]
      (is (thrown-with-msg? Exception #"failed"
                            (op :own/update t (fn [_] (swap! calls inc) (throw (Exception. "failed"))))))
      (is (= 1 @calls))
      (is (= :open (:status (a/state t))))
      (is (= 3 (op :own/read t)))
      (op :own/update t (fn [v]
                         (is (thrown-with-msg? clojure.lang.ExceptionInfo #"advancing" (op :own/read t)))
                         (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned write share"
                                               (a/open-fork! {} 2 [])))
                         (inc v)))
      (is (= 4 (op :own/freeze t))))))

(deftest owned-concurrent-transitions
  (binding [a/*store* (a/new-store)]
    (let [t (op :own/alloc :once)
          start (promise)
          fs (mapv (fn [_] (future @start (try (op :own/move t) (catch Exception _ nil)))) (range 16))]
      (deliver start true)
      (let [winners (keep deref fs)]
        (is (= 1 (count winners)))
        (is (= 1 (mass)))
        (is (= :once (op :own/freeze (first winners))))))
    (let [t (op :own/alloc :loans)
          start (promise)
          fs (mapv (fn [_] (future @start (try (a/borrow-owned! t 1/8 []) (catch Exception _ nil)))) (range 32))]
      (deliver start true)
      (let [loans (vec (keep deref fs))]
        (is (= 8 (count loans)))
        (is (= 1 (mass)))
        (run! a/return-owned! loans)
        (is (= 1 (mass)))
        (op :own/drop t)))))

(deftest owned-generated-walk
  (binding [a/*store* (a/new-store)]
    (let [rng (java.util.Random. 1005)
          owner (atom (op :own/alloc []))
          value (atom [])]
      (dotimes [i 200]
        (case (.nextInt rng 4)
          0 (do (op :own/update @owner conj i) (swap! value conj i))
          1 (reset! owner (op :own/move @owner))
          2 (a/with-owned-borrow @owner 1 []
              (fn [b]
                (let [g (a/open-fork! {} (inc (.nextInt rng 4)) [])]
                  (doseq [j (range (:n @g))]
                    (is (= @value (a/op! :own/read [b] (frames g j)))))
                  (is (= 1 (mass)))
                  (a/close-group! g [] (if (.nextBoolean rng) :exit :abort)))))
          3 (a/with-owned-borrow @owner 1/2 []
              (fn [b] (a/with-owned-borrow b 1/4 []
                        (fn [c] (is (= @value (op :own/read c))) (is (= 1 (mass))))))))
        (is (= @value (op :own/read @owner)))
        (is (= 1 (mass))))
      (is (= @value (op :own/freeze @owner)))
      (is (zero? (mass))))))
