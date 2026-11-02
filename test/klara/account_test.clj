(ns klara.account-test
  "Accounts (design/10-accounting.md, spec/L3-effects.md#accounts): the
  cases a conformance file cannot state, and conservation over generated
  programs (L3.account.conservation)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]
            [klara.runtime.account :as acct]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(def ^:private header
  "(ns acc (:require [klara.account :as a] [klara.job :as job]
                     [klara.effect :refer [perform handle]]))
   (defn rule-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))")

(defn- run [src] (let [s (session)] (k/eval-string s (str header src))))

(defn- root [s] (acct/state (:wallet @s)))

(deftest tokens-move-linearly   ; L3.affine.reuse L3.account.token
  (testing "a second use through any route is refused"
    (is (= [:L3.affine.reuse :L3.affine.reuse :L3.affine.reuse :L3.affine.reuse]
           (run "(a/mint! {:eur 4})
                 (def kept (a/take {:eur 1}))
                 (let [t (a/take {:eur 1}) alias t
                       v [(a/take {:eur 1})]
                       c (let [u (a/take {:eur 1})] (fn [] (a/put u)))]
                   (a/put t) (a/put (first v)) (c) (a/put kept)
                   [(rule-of #(a/put alias)) (rule-of #(a/spend (first v) {:eur 1})) (rule-of c)
                    (rule-of #(a/balance kept))])"))))
  (testing "join refuses the same token twice"
    (is (= :L3.affine.reuse (run "(a/mint! {:eur 1}) (let [t (a/take {:eur 1})] (rule-of #(a/join t t)))"))))
  (testing "a token made through interop is not live"
    (is (#{:L3.affine.reuse :L3.account.foreign}
         (run "(a/mint! {:eur 1}) (rule-of #(a/put (klara.runtime.value.Token. 1)))")))))

(deftest tokens-belong-to-their-job   ; L3.account.foreign L3.job.resume L3.job.parallel
  (testing "a token returned out of its job was put back when the job settled"
    (is (= [:L3.account.foreign {:eur 2}]
           (run "(a/mint! {:eur 2})
                 (let [o (job/run {:budget {:eur 1}} (fn [] (a/take {:eur 1})))]
                   [(rule-of #(a/put (:value o))) (a/wallet)])"))))
  (testing "a moved token cannot be used again by the parent"
    (is (= :L3.affine.reuse
           (run "(a/mint! {:eur 1})
                 (let [t (a/take {:eur 1})] (job/run {:budget t} (fn [] 1)) (rule-of #(a/put t)))"))))
  (testing "after resume, tokens taken before the exhaustion are foreign"
    (is (= [:done :L3.account.foreign]
           (run "(a/mint! {:eur 2})
                 (let [o (job/run {:budget {:steps 30 :eur 1}}
                                  (fn [] (let [t (a/take {:eur 1})]
                                           (loop [i 0] (if (< i 100) (recur (inc i)) nil))
                                           (rule-of #(a/put t)))))
                       r (job/resume o {:steps 1000})]
                   [(:status r) (:value r)])"))))
  (testing "parallel jobs take vectors"
    (is (= :L3.job.parallel
           (run "(a/mint! {:eur 1}) (rule-of #(job/run-all {:budget (a/take {:eur 1})} [(fn [] 1)]))")))))

(deftest settlement-keeps-what-was-spent   ; L3.account.settle L3.budget.exhausted
  (testing "spending inside a host call that ran out of steps stays spent"
    (let [s (session)
          o (k/eval-string s (str header "(a/mint! {:eur 1000})
                (job/run {:budget {:steps 40 :eur 1000}} (fn [] (mapv (fn [x] (a/spend! {:eur 1}) x) (range 100))))"))]
      (is (= :exhausted (:status o)))
      (is (false? (:resumable o)))
      (let [{:keys [balance spent minted]} (root s)]
        (is (pos? (:eur spent 0)))
        (is (= minted (acct/v+ balance spent))))))
  (testing "a discarded job is still charged"
    (is (= {:eur 9}
           (run "(a/mint! {:eur 10}) (job/run {:budget {:eur 5}} (fn [] (a/spend! {:eur 1}))) (a/wallet)"))))
  (testing "steps budgets keep their shape"
    (is (= [{:steps 1} true]
           (run "(let [o (job/run {:budget {:steps 100}} (fn [] 1))] [(:spent o) (contains? (:receipt o) :id)])")))))

(deftest parallel-jobs-settle-exactly   ; L3.job.parallel L3.account.receipt
  (let [s (session)
        r (k/eval-string s (str header "(a/mint! {:db 8 :eur 160})
            (loop [i 0 ok true]
              (if (< i 20)
                (let [os (job/run-all {:budget {:db 1 :eur 1 :steps 1000}}
                                      (vec (repeat 8 (fn [] (a/spend! {:eur 1/2})
                                                       (let [t (a/take {:eur 1/4})] (a/spend t {:eur 1/8}))
                                                       (a/holds? (a/take {:db 1}) {:db 1})))))]
                  (recur (inc i) (and ok (every? :value os) (= {:db 8} (select-keys (a/wallet) [:db])))))
                ok))"))]
    (is (true? r))
    (let [{:keys [balance spent minted live]} (root s)]
      (is (empty? live))
      (is (= {:eur 100} spent))
      (is (= minted (acct/v+ balance spent))))))

;; ---------------------------------------------------------------------------
;; Conservation over generated programs (L3.account.conservation)

(def ^:private resources [:r1 :r2])

(defn- rvec [^java.util.Random r]
  (into {} (for [k resources :when (.nextBoolean r)] [k (/ (.nextInt r 5) (inc (.nextInt r 2)))])))

(defn- gen-op [^java.util.Random r depth]
  (let [pick #(list 'pick 'ts (.nextInt r 8))
        sub (fn [] (list 'fn [] (list* 'let ['ts '(atom [])] (repeatedly (inc (.nextInt r 5)) #(gen-op r (dec depth))))))
        steps #(case (.nextInt r 3) 0 {:steps (+ 5 (.nextInt r 40))} 1 {:steps 2000} {})
        op (case (.nextInt r (if (pos? depth) 12 8))
             0 (list 'a/spend! (rvec r))
             1 (list 'swap! 'ts 'conj (list 'a/take (rvec r)))
             2 (list 'swap! 'ts 'conj (list 'a/spend (pick) (rvec r)))
             3 (list 'swap! 'ts 'into (list 'a/split (pick) (rvec r)))
             4 (list 'swap! 'ts 'conj (list 'a/join (pick) (pick)))
             5 (list 'a/put (pick))
             6 (list 'a/holds? (pick) (rvec r))
             7 '(loop [i 0] (if (< i 20) (recur (inc i)) nil))
             8 (list 'job/run {:budget (merge (rvec r) (steps))} (sub))
             9 (list 'job/run {:budget (pick)} (sub))
             10 (list 'let ['o (list 'job/run {:budget (merge (rvec r) {:steps 25})} (sub))]
                      (list 'when '(= :exhausted (:status o)) (list 'job/resume 'o (merge (rvec r) (steps)))))
             11 (list 'job/run {:budget (merge (rvec r) {:steps 30})}
                      (list 'fn [] (list 'mapv (list 'fn ['x] (list 'a/spend! (rvec r)) 'x) '(range 50)))))]
    (list 'try op '(catch Exception e nil))))

(defn- program [seed]
  (let [r (java.util.Random. seed)]
    (cons '(def ts (atom [])) (repeatedly 12 #(gen-op r 2)))))

(defn- balanced? [{:keys [granted spent returned]}] (= granted (merge-with +' spent returned)))

(deftest conservation-holds-for-random-programs   ; L3.account.conservation
  (let [receipts (atom [])
        settle acct/settle!]
    (with-redefs [acct/settle! (fn [& args] (let [r (apply settle args)] (swap! receipts conj r) r))]
      (doseq [seed (range 150)]
        (let [s (session)]
          (k/eval-string s "(ns gen (:require [klara.account :as a] [klara.job :as job]))
                            (defn pick [ts i] (let [c @ts] (when (seq c) (nth c (mod i (count c))))))
                            (a/mint! {:r1 20 :r2 20})")
          (doseq [form (program seed)]
            (k/eval-string s (pr-str form))
            (let [{:keys [balance spent minted live]} (root s)
                  held (reduce acct/v+ balance (vals live))]
              (is (= minted (acct/v+ held spent)) (str "seed " seed " after " (pr-str form))))))))
    (is (< 100 (count @receipts)))
    (is (every? balanced? @receipts))))
