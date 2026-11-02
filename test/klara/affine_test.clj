(ns klara.affine-test
  "The declared affine subset (L4.check.affine, design/04-ownership.md,
  design/10-accounting.md): definitions it accepts run as before; each
  clause of the judgment rejects a definition, naming the clause and the
  place."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]
            [klara.runtime.session]))

(defn- session []
  (doto (k/session {:roots ["lib"] :out (java.io.StringWriter.)})
    (k/eval-string "(ns af (:require [klara.account :as a] [klara.job :as job]))
                    (a/mint! {:eur 10 :db 3})")))

(def ^:private library
  "(defaffine add-all [^:own acc xs]
     (loop [i 0 acc acc] (if (< i (count xs)) (recur (inc i) (conj! acc (nth xs i))) acc)))
   (defaffine histogram [words]
     (loop [i 0 counts (own {})]
       (if (< i (count words))
         (let [w (nth words i)] (recur (inc i) (assoc! counts w (inc (get counts w 0)))))
         (persistent! counts))))
   (defaffine ask [^:own money q] [(a/spend money {:eur 1/4}) (str \"answer \" q)])
   (defaffine query [^:borrow permit q] (if (a/holds? permit {:db 1}) [:rows q] nil))
   (defaffine answer [q]
     (let [money (a/take {:eur 1}) permit (a/take {:db 1})
           [money a1] (ask money q)
           r (query permit q)
           [money a2] (ask money (str a1 r))]
       (a/put permit) (a/put money) a2))
   (defaffine halves [^:own t] (let [[x y] (a/split t {:eur 1/2})] (a/join x y)))
   (defaffine thread [^:own t] (loop [i 0 t t] (if (< i 3) (recur (inc i) t) t)))
   (defn asks [] (klara.effect/perform :ask 1))
   (defn twice [x] (* 2 x))")

(deftest declared-definitions-run-as-before   ; L4.check.affine
  (let [s (session)]
    (k/eval-string s library)
    (is (= [1 2 3] (k/eval-string s "(persistent! (add-all (own [1]) [2 3]))")))
    (is (= {"a" 2 "b" 1} (k/eval-string s "(histogram [\"a\" \"b\" \"a\"])")))
    (is (= "answer answer q[:rows \"q\"]" (k/eval-string s "(answer \"q\")")))
    (is (= {:eur 19/2 :db 3} (k/eval-string s "(a/wallet)")))
    (is (= {:eur 1} (k/eval-string s "(let [t (halves (a/take {:eur 1}))] (let [b (a/balance t)] (a/put t) b))")))
    (testing "the declaration callers are checked against"
      (is (= {:own #{0} :borrow #{} :returns {:tuple #{0}} :premises #{}}
             (get-in ((:defined (klara.runtime.session/resolver s 'af)) 'af/ask) [:meta :klara/affine]))))
    (testing "an undeclared caller is still checked at run time"
      (is (= :L3.affine.reuse
             (k/eval-string s "(let [t (a/take {:eur 1})] (ask t 1)
                                 (try (ask t 2) nil (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))"))))))

(defn- rejection [src]
  (let [s (session)]
    (k/eval-string s library)
    (try (k/eval-string s src) nil
         (catch clojure.lang.ExceptionInfo e (select-keys (ex-data e) [:rule :clause :local :place])))))

(deftest each-clause-rejects   ; L4.check.affine
  (doseq [[clause local src]
          [[1 nil "(defaffine no-token [x] (conj! [] x))"]
           [2 "t" "(defaffine twice [^:own t] (a/put t) (a/put t))"]
           [2 "acc" "(defaffine read-after [^:own acc] (let [acc2 (conj! acc 1)] (count acc) acc2))"]
           [2 "t" "(defaffine join-self [^:own t] (a/join t t))"]
           [3 nil "(defaffine branch [^:own t c] (if c (a/put t) nil))"]
           [4 "t" "(defaffine capture [^:own t] (fn [] (a/put t)))"]
           [4 "t" "(defaffine store [^:own t] {:t t})"]
           [4 "t" "(defaffine host [^:own t] (println t) t)"]
           [4 "t" "(defaffine undeclared [^:own t] (identity t))"]
           [4 "b" "(defaffine borrow-consume [^:borrow b] (a/put b))"]
           [6 nil "(defaffine careless [q] (let [money (a/take {:eur 1})] (ask money q) (ask money q)))"]
           [6 "t" "(defaffine leak [q] (let [t (a/take {:eur 1})] q))"]
           [6 "t" "(defaffine bad-recur [^:own t] (loop [i 0 t t] (if (< i 3) (recur (inc i) (a/take {:eur 1})) (a/put t))))"]
           [6 "x" "(defaffine half-dropped [^:own t] (let [[x y] (a/split t {:eur 1/2})] (a/put y)))"]
           ;; try: no token out of it, nothing consumed twice, arms only read
           [4 nil "(defaffine launder [] (conj [] (try (a/take {:eur 1}) (catch Exception e nil))))"]
           [2 "t" "(defaffine after-try [^:own t] (try (a/put t) (catch Exception e nil)) (a/put t))"]
           [3 nil "(defaffine catch-put [^:own t] (try (a/holds? t {:eur 1}) (catch Exception e (a/put t))) t)"]
           [3 nil "(defaffine finally-put [^:own t] (try 1 (finally (a/put t))) t)"]
           ;; no part of another form may give a token
           [4 nil "(defaffine stash [] (def stashed (a/take {:eur 1})) nil)"]
           [4 "t" "(defaffine quoted [^:own t] (klara.stage/code (a/put t)))"]
           [4 nil "(defaffine thrown [] (throw (ex-info \"x\" {:t (a/take {:eur 1})})))"]
           ;; clause 7: no token live where the computation may be captured
           [7 "t" "(defaffine pf [] (let [t (a/take {:eur 1})] (klara.effect/perform :ask 1) (a/put t)))"]
           [7 "t" "(defaffine via [^:own t] (asks) t)"]
           [7 "t" "(defaffine via-local [^:own t f] (f) t)"]
           [7 "t" "(defaffine defining [^:own t] (def z 1) t)"]
           [7 "t" "(defaffine printing [^:own t] (println 1) t)"]
           [7 "b" "(defaffine borrowed [^:borrow b] (asks) nil)"]]]
    (testing src
      (let [r (rejection src)]
        (is (= :L4.check.affine (:rule r)))
        (is (= clause (:clause r)))
        (is (= local (some-> (:local r) str)))
        (is (some? (:place r)) (pr-str r))))))

(deftest try-and-calls-under-tokens   ; L4.check.affine
  (let [s (session)]
    (k/eval-string s library)
    (k/eval-string s "(defaffine guarded [^:own t] (try (a/put t) (catch Exception e nil)) :done)
                      (defaffine reads [^:own t] (let [ok (try (a/holds? t {:eur 1}) (catch Exception e false))] (a/put t) ok))
                      (defaffine pure-call [^:own t] (let [n (twice 2)] (a/put t) n))
                      (defaffine in-job [^:own t] (let [o (job/run {} asks)] (a/put t) (:status o)))")
    (is (= [:done true 4 :failed {:eur 10 :db 3}]
           (k/eval-string s "[(guarded (a/take {:eur 1})) (reads (a/take {:eur 1})) (pure-call (a/take {:eur 1}))
                              (in-job (a/take {:eur 1})) (a/wallet)]")))
    (testing "the effect facts relied on are recorded as premises"
      (is (contains? (set (map first (get-in ((:defined (klara.runtime.session/resolver s 'af)) 'af/pure-call)
                                             [:meta :klara/affine :premises])))
                     'af/twice)))))

(deftest a-rejected-definition-is-not-defined   ; L4.check.affine
  (let [s (session)]
    (try (k/eval-string s "(defaffine leak [q] (let [t (a/take {:eur 1})] q))") (catch Exception _))
    (is (= :L1.resolve.unbound
           (try (k/eval-string s "(leak 1)") (catch clojure.lang.ExceptionInfo e (:rule (ex-data e))))))))
