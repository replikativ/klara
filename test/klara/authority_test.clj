(ns klara.authority-test
  "RFC 0001 in T0 (S6): authority tokens, fork, settlement, fork-resume,
  deferred irreversible effects.

  - adversarial suite (AU1, Codex experiment 1): duplicate locals,
    nested collections, metadata, escaping closures, lookup after
    capture, repeated resume, cancellation;
  - spindel-style settlement (AU2, AU3): exactly once, mutually
    exclusive, partition disjoint and exhaustive, fail closed,
    :incomplete after a partial mutation, the :advancing lease;
  - evidence mass conservation over fork/split/join/discard (AU6);
  - deferred intents run iff the branch is adopted (AU5)."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [klara.authority :as a]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]))

(defn- session []
  (let [wo (w/make-world)] {:world wo :fiber (w/fiber wo) :store (a/new-store)}))

(defn- k!
  "Evaluate or define form in the session (raising its fiber first)."
  [{:keys [world fiber store]} form]
  (w/raise-basis! fiber)
  (binding [ev/*fiber* fiber a/*store* store]
    (if (and (seq? form) ('#{def defn defmacro} (first form)))
      (:name (d/define! world form))
      (d/eval-in fiber form))))

(defn- err
  "The message of the error form raises, or ::no-error."
  [s form]
  (try (k! s form) ::no-error
       (catch Throwable t (or (ex-message t) (str t)))))

(defn- st [s t] (binding [a/*store* (:store s)] (select-keys (a/state t) [:kind :status :operation])))

(def split2 '{:split (fn [k] [(k :l) (k :r)])})

;; ---------------------------------------------------------------------------
;; AU1: no program duplicates an authority
;; ---------------------------------------------------------------------------

(deftest duplicate-locals
  (let [s (session)]
    (is (re-find #"consume!: authority is settled"
                 (err s '(let [r (resource 1) a r b r] (consume! a) (consume! b))))
        "two locals, one authority: the second use finds it settled")
    (is (re-find #"not transferred"
                 (err s '(let [r (resource 1) a r b r] (fork [x (consume! a) y (consume! b)]))))
        "a fork never gives a resource to two branches")
    (is (re-find #"not transferred"
                 (err s '(let [r (resource 1) a r b r] (fork {:transfer {r 0}} [x (consume! a) y (consume! b)])))))
    (is (= [1 :y] (k! s '(let [r (resource 1) a r b r] (fork {:transfer {b 0}} [x (consume! a) y :y]))))
        "aliases name one authority: transferring b transfers a")
    (is (re-find #"exactly one branch"
                 (err s '(let [r (resource 1)] (fork {:transfer {r [0 1]}} [x 1 y 2])))))
    (is (re-find #"appears twice" (err s '(let [e (evidence 1) f e] (join [e f])))))))

(deftest nested-collections-and-metadata
  (let [s (session)]
    (is (re-find #"not transferred"
                 (err s '(let [r (resource 1) m {:deep [#{r}]}]
                           (fork {:transfer {r 0}} [x :x y (consume! (first (first (:deep m))))])))))
    (testing "a continuation capturing an authority deep in a collection is resumed once only"
      (is (re-find #"fork-resume: the continuation captured a resource"
                   (err s (list 'let '[r (resource 1) m {:deep [#{r}]}]
                                (list 'handle ['h split2] '(do (perform h :split) (count m))))))))
    (testing "... or in metadata"
      (is (re-find #"fork-resume: the continuation captured a resource"
                   (err s (list 'let '[r (resource 1) v (with-meta [1 2] {:auth r})]
                                (list 'handle ['h split2] '(do (perform h :split) (count v))))))))
    (testing "... or in a closure's captures"
      (is (re-find #"fork-resume: the continuation captured an evidence"
                   (err s (list 'let '[e (evidence 1) f (fn [] (spend! e 1/2))]
                                (list 'handle ['h split2] '(do (perform h :split) f)))))))
    (testing "data holding an authority is still freely copied"
      (is (= 3 (count (k! s '(let [r (resource 1)] [r r {:r r}]))))))))

(deftest escaping-closures
  (let [s (session)]
    (k! s '(def r (resource :file)))
    (is (re-find #"authority is advancing \(fork\)"
                 (err s '(fork {:transfer {r 0}} [x (fn [] (consume! r))] ((:value x)))))
        "during the fork scope the parent's authority is leased")
    (k! s '(def f (fork {:transfer {r 0}} [x (fn [] (consume! r))] (:value x))))
    (is (= :file (k! s '(f))) "after the fork the authority is the parent's again")
    (is (re-find #"settled" (err s '(f))))
    (k! s '(def g (fork [x (let [e (evidence 1)] (fn [] (spend! e 1/2)))] (:value x))))
    (is (re-find #"settled \(discard\)" (err s '(g)))
        "a discarded branch's authorities die with it, whoever holds them")
    (k! s '(def g2 (fork [x (let [e (evidence 1)] (fn [] (spend! e 1/2)))] (adopt! x) (:value x))))
    (is (= 1/2 (k! s '(g2))) "an adopted branch's authorities move to the parent")
    (k! s '(def leak (atom nil)))
    (k! s '(fork [x (let [e (evidence 1)] (reset! leak e))]))
    (is (nil? (k! s '(deref leak))) "a discarded branch's reset! never ran")
    (is (nil? (k! s '(fork [x (let [e (evidence 1)] (reset! leak e) :x)] (adopt! x) (deref leak))))
        "the adopted branch's reset! runs at the scope exit, after the body")
    (is (= 1/2 (k! s '(spend! (deref leak) 1/2))) "and hands over an authority the parent now owns")))

(deftest lookup-after-capture
  (let [s (session)]
    (k! s '(def r (resource 1)))
    (testing "a branch resolving a resource from the world is checked at the use"
      (is (re-find #"not transferred" (err s '(fork [x (consume! r)])))))
    (testing "a resumed continuation that reaches a resource only through the world"
      (is (re-find #"fork-resume: a resumed continuation uses a resource"
                   (err s (list 'handle ['h split2] '(do (perform h :split) (use! r identity))))))
      (is (= {:kind :resource :status :open} (st s (k! s 'r)))
          "the first resumption used it; the second was refused at its use")
      (is (re-find #"settled \(consume\)"
                   (err s (list 'handle ['h split2] '(do (perform h :split) (consume! r))))))
      (is (= {:kind :resource :status :settled :operation :consume} (st s (k! s 'r)))
          "consumed by the first resumption, so the second finds it settled"))))

(deftest repeated-resume
  (let [s (session)]
    (k! s '(def g (rand-key 7)))
    (testing "randomness is split per resumption: no two shots share a stream"
      (let [[[a1 a2] [b1 b2]] (k! s (list 'handle ['h split2]
                                          '(do (perform h :split) [(draw! g) (draw! g)])))]
        (is (= 4 (count (distinct [a1 a2 b1 b2]))))))
    (testing "an evidence authority used in a second shot is refused (split it explicitly)"
      (k! s '(def e (evidence 1)))
      (is (re-find #"fork-resume: a resumed continuation uses an evidence"
                   (err s (list 'handle ['h split2] '(do (perform h :split) (spend! e 1/4)))))))
    (testing "a budget is borrowed by each shot and charged once"
      (k! s '(def b (budget 10)))
      (is (= [{:units 7} {:units 4}]
             (k! s (list 'handle ['h split2] '(do (perform h :split) (spend! b 3))))))
      (is (= {:units 4} (k! s '(remaining b))))
      (is (re-find #"hard budget" (err s (list 'handle ['h split2] '(do (perform h :split) (spend! b 3)))))
          "hard components cannot be overspent across shots"))
    (testing "a continuation that captured an open fork cannot be resumed twice"
      (is (re-find #"captured a running fork branch|the fork has closed"
                   (err s (list 'handle ['h split2] '(fork [x (perform h :split)] (:value x)))))))
    (testing "multi-shot over plain data is unchanged"
      (is (= [{:b :l} {:b :r}] (k! s (list 'handle ['h split2] '{:b (perform h :split)})))))))

(deftest cancellation
  (let [s (session)]
    (k! s '(def e (evidence 1)))
    (k! s '(def r (resource :r)))
    (k! s '(def log (atom [])))
    (is (= :caught (k! s '(try (fork {:transfer {r 1}}
                                     [x (do (spend! e 1/4) (swap! log conj :x))
                                      y (do (consume! r) (throw (ex-info "boom" {})))]
                                     (adopt! x))
                               (catch Exception _ :caught)))))
    (is (= 1 (k! s '(remaining e))) "a cancelled fork refunds its evidence")
    (is (= [] (k! s '(deref log))) "and drops its intents")
    (is (= {:kind :resource :status :settled :operation :consume} (st s (k! s 'r)))
        "a resource consumed before the failure stays consumed (irreversible)")
    (k! s '(def r2 (resource :r2)))
    (is (= :caught (k! s '(try (fork {:transfer {r2 0}} [x (throw (ex-info "early" {}))] 1)
                               (catch Exception _ :caught)))))
    (is (= :r2 (k! s '(consume! r2))) "an unconsumed resource returns to the parent")
    (is (= :caught (k! s '(try (fork [x (spend! e 1/2)] (adopt! x) (throw (ex-info "late" {})))
                               (catch Exception _ :caught)))))
    (is (= 1 (k! s '(remaining e))) "an exception in the fork body discards even the adopted branch")
    (is (= {:kind :evidence :status :open} (st s (k! s 'e))))))

;; ---------------------------------------------------------------------------
;; AU2, AU3: settlement (port of spindel's ForkHandle tests)
;; ---------------------------------------------------------------------------

(defn- systems-session []
  (let [s (session)]
    (k! s '(def kb (perform :world/fork)))
    (k! s '(def repo (perform :world/fork)))
    (k! s '(def h (branch! {:kb kb :repo repo})))
    s))

(deftest settlement-exactly-once
  (let [s (systems-session)]
    (k! s '(perform :world/eval-in (system h :kb) '(def fact 1)))
    (is (re-find #"unable to resolve fact" (err s '(perform :world/eval-in kb 'fact))) "branch writes are isolated")
    (is (= {:merged [:kb :repo]} (k! s '(merge! h))))
    (is (= 1 (k! s '(perform :world/eval-in kb 'fact))))
    (is (= {:merged [:kb :repo]} (k! s '(merge! h))) "repeating the settlement returns its result")
    (is (re-find #"discard!: authority is settled \(merge\)" (err s '(discard! h)))
        "merge and discard are mutually exclusive")
    (is (re-find #"system: authority is settled" (err s '(system h :kb)))))
  (let [s (systems-session)]
    (is (= {:discarded [:kb :repo]} (k! s '(discard! h))))
    (is (re-find #"merge!: authority is settled \(discard\)" (err s '(merge! h)))))
  (testing "transfer makes the old token stale"
    (let [s (systems-session)]
      (k! s '(def h2 (transfer! h :review)))
      (is (re-find #"settled \(transfer\)" (err s '(merge! h))))
      (is (= {:kind :branchable :status :open :owner :review} (k! s '(status h2))))
      (is (= {:merged [:kb :repo]} (k! s '(merge! h2)))))))

(deftest partition-disjoint-exhaustive
  (let [s (systems-session)
        bad {"overlap" '[{:systems #{:kb :repo} :owner :a} {:systems #{:kb} :owner :b}]
             "omitted" '[{:systems #{:kb} :owner :a}  {:systems #{} :owner :b}]
             "cover the systems exactly" '[{:systems #{:kb} :owner :a} {:systems #{:x} :owner :b}]
             "at least two" '[{:systems #{:kb :repo} :owner :a}]
             "owner" '[{:systems #{:kb} :owner :a} {:systems #{:repo}}]}]
    (doseq [[msg parts] bad]
      (is (not= ::no-error (err s (list 'partition! 'h (list 'quote parts)))) msg)
      (is (= {:kind :branchable :status :open} (k! s '(status h)))
          (str "a rejected partition (" msg ") does not consume the authority")))
    (k! s '(def parts (partition! h '[{:systems #{:kb} :owner :kr} {:systems #{:repo} :owner :rr}])))
    (is (= {:kind :branchable :status :settled :operation :partition} (k! s '(status h)))
        "partition consumes the parent")
    (is (re-find #"settled \(partition\)" (err s '(merge! h))))
    (k! s '(perform :world/eval-in (system (first parts) :kb) '(def a 1)))
    (k! s '(perform :world/eval-in (system (second parts) :repo) '(def b 2)))
    (is (re-find #"no system :repo" (err s '(system (first parts) :repo))) "each part governs its systems only")
    (is (= {:merged [:kb]} (k! s '(merge! (first parts)))))
    (is (= {:discarded [:repo]} (k! s '(discard! (second parts)))))
    (is (= 1 (k! s '(perform :world/eval-in kb 'a))))
    (is (re-find #"unable to resolve b" (err s '(perform :world/eval-in repo 'b))))))

(deftest fail-closed
  (testing "a preflight failure (conflict) reopens the authority"
    (let [s (systems-session)]
      (k! s '(perform :world/eval-in (system h :kb) '(def x :branch)))
      (k! s '(perform :world/eval-in kb '(def x :parent)))
      (is (re-find #"conflict: x" (err s '(merge! h))))
      (is (= {:kind :branchable :status :open} (k! s '(status h))))
      (is (= {:discarded [:kb :repo]} (k! s '(discard! h))) "still settleable")))
  (testing "disjoint writes merge (the branch rebases over the parent)"
    (let [s (systems-session)]
      (k! s '(perform :world/eval-in (system h :kb) '(def x :branch)))
      (k! s '(perform :world/eval-in kb '(def y :parent)))
      (is (= {:merged [:kb :repo]} (k! s '(merge! h))))
      (is (= [:branch :parent] (k! s '(perform :world/eval-in kb '[x y]))))))
  (testing "a failure after the first durable mutation leaves :incomplete"
    (let [s (systems-session)]
      (k! s '(perform :world/eval-in (system h :kb) '(def x 1)))
      (k! s '(perform :world/eval-in (system h :repo) '(def y 1)))
      (binding [a/*mutation-hook* (fn [_ sid] (when (= :repo sid) (throw (ex-info "disk full" {}))))]
        (is (re-find #"disk full" (err s '(merge! h)))))
      (is (= {:kind :branchable :status :incomplete :operation :merge} (k! s '(status h))))
      (is (= 1 (k! s '(perform :world/eval-in kb 'x))) "kb was merged before the failure")
      (is (re-find #"authority is incomplete" (err s '(merge! h))) "no second settlement")
      (is (re-find #"authority is incomplete" (err s '(discard! h))))))
  (testing "a race between preflight and mutation is detected, not lost"
    (let [s (systems-session)]
      (k! s '(perform :world/eval-in (system h :kb) '(def x 1)))
      (binding [a/*mutation-hook* (fn [_ sid] (when (= :kb sid) (k! s '(perform :world/eval-in kb '(def z 0)))))]
        (is (re-find #"changed during the merge" (err s '(merge! h)))))
      (is (= {:kind :branchable :status :incomplete :operation :merge} (k! s '(status h))))))
  (testing "the :advancing lease excludes settlement"
    (let [s (systems-session)
          seen (atom nil)]
      (k! s '(perform :world/eval-in kb '(def p 1)))
      (binding [a/*mutation-hook* (fn [_ _] (when-not @seen (reset! seen (err s '(merge! h)))))]
        (is (= {:advanced [:kb :repo]} (k! s '(advance! h)))))
      (is (re-find #"merge!: authority is advancing" @seen))
      (is (= {:kind :branchable :status :open} (k! s '(status h))))
      (is (= 1 (k! s '(perform :world/eval-in (system h :kb) 'p))) "the branch now sees the parent's write"))))

(deftest fork-partitions-settlement
  (let [s (systems-session)]
    (is (= [:a :b]
           (k! s '(fork [x (do (perform :world/eval-in (system h :kb) '(def v :a)) :a)
                         y (do (perform :world/eval-in (system h :kb) '(def v :b)) :b)]
                    (adopt! y)
                    [(:value x) (:value y)]))))
    (is (= :b (k! s '(perform :world/eval-in (system h :kb) 'v)))
        "the adopted branch merged into h's branch, the other was discarded")
    (is (re-find #"unable to resolve v" (err s '(perform :world/eval-in kb 'v))) "h itself is not settled by the fork")
    (is (= {:kind :branchable :status :open} (k! s '(status h))))
    (is (re-find #"only one branch" (err s '(fork [x 1 y 2] (adopt! x) (adopt! y)))))))

;; ---------------------------------------------------------------------------
;; budgets and randomness at forks
;; ---------------------------------------------------------------------------

(deftest budget-and-randomness-split
  (let [s (session)]
    (k! s '(def b (budget {:time 10 :money 4} #{:time})))
    (is (re-find #"hard budget component :time" (err s '(fork [x (spend! b {:time 6}) y 0]))))
    (is (= [{:time 1 :money 2} {:time 5 :money -1}]
           (k! s '(fork [x (spend! b {:time 4}) y (spend! b {:money 3})]))))
    (is (= {:time 6 :money 1} (k! s '(remaining b))) "spending in discarded branches is charged")
    (is (= [{:time 1 :money 1}] (k! s '(fork {:shares {b [1]}} [x (spend! b {:time 5})]))))
    (k! s '(def g (rand-key 42)))
    (let [[x y] (k! s '(fork [x (draw! g) y (draw! g)]))
          [cx cy] (k! s '(fork :coupled [x (draw! g) y (draw! g)]))
          [px py] (k! s '(fork {:coupled [g]} [x (draw! g) y (draw! g)]))]
      (is (not= x y) "split keys by default")
      (is (= cx cy) ":coupled shares the key")
      (is (= px py))
      (is (not= cx px) "the parent's key moves on after each fork"))))

;; ---------------------------------------------------------------------------
;; AU6: evidence mass is conserved across fork / split / join / discard
;; ---------------------------------------------------------------------------

(defn- conserved? [s]
  (binding [a/*store* (:store s)] (= (a/evidence-held) (a/evidence-minted))))

(deftest evidence-conservation
  (let [s (session)]
    (k! s '(def e (evidence 1)))
    (is (= [1/4 1/4 1/2] (k! s '(fork {:shares {e [1 1 2]}} [x (remaining e) y (remaining e) z (remaining e)]))))
    (is (= [:in-branch true] (k! s '(fork [x (do (spend! e 1/8) [:in-branch (klara.authority/evidence-held)])]
                                     [(first (:value x)) (= (second (:value x)) (klara.authority/evidence-minted))]))))
    (is (conserved? s))
    (is (re-find #"overspent" (err s '(fork [x (spend! e 1/2) y (spend! e 3/4)]))) "a branch spends only its share")
    (is (= 1 (k! s '(remaining e))))
    (k! s '(fork [x (let [[p q] (split e 2)] (spend! p 1/4) (evidence 5)) y (spend! e 1/4)] (adopt! x)))
    (is (conserved? s) "split and a fresh mint in the adopted branch, spending in the discarded one")
    (is (= 6 (binding [a/*store* (:store s)] (a/evidence-minted))))
    (k! s '(fork [x (evidence 7)]))
    (is (= 6 (binding [a/*store* (:store s)] (a/evidence-minted))) "a mint in a discarded branch is undone")
    (is (conserved? s)))
  (testing "a random walk over fork/split/join/spend/discard/adopt/cancel"
    (let [s (session)
          rng (java.util.Random. 2026)
          pick (fn [xs] (nth xs (.nextInt rng (count xs))))
          pool (atom (vec (for [m [1 2 3/2]] (k! s (list 'evidence m)))))
          open? (fn [t] (= :open (:status (st s t))))]
      (dotimes [_ 200]
        (swap! pool #(filterv open? %))
        (when (empty? @pool) (swap! pool conj (k! s '(evidence 1))))
        (let [t (pick @pool)
              rem (k! s (list 'remaining t))]
          (case (.nextInt rng 6)
            0 (swap! pool into (k! s (list 'split t (inc (.nextInt rng 3)))))
            1 (let [u (pick @pool)]
                (when-not (= t u) (swap! pool conj (k! s (list 'join [t u])))))
            2 (k! s (list 'spend! t (/ rem 3)))
            3 (let [ad (.nextInt rng 3)]
                (when-let [made (k! s (list 'fork ['x (list 'do (list 'spend! t (/ rem 4)) (list 'split t 2))
                                                    'y (list 'spend! t (/ rem 5))]
                                            (list 'when (< ad 2) (list 'adopt! (if (zero? ad) 'x 'y)))
                                            (list 'when (zero? ad) '(:value x))))]
                  (swap! pool into made)))
            4 (k! s (list 'try (list 'fork ['x (list 'do (list 'spend! t (/ rem 2)) '(throw (ex-info "x" {})))] 1)
                          '(catch Exception _ nil)))
            5 (k! s (list 'fork ['x (list 'spend! t (/ rem 2))]))))
        (is (conserved? s)))
      (is (pos? (count @pool))))))

;; ---------------------------------------------------------------------------
;; AU5: deferred intents run iff the branch is adopted
;; ---------------------------------------------------------------------------

(deftest intents-run-iff-adopted
  (let [s (session)]
    (k! s '(def log (atom [])))
    (is (= :ok (k! s '(fork [x (swap! log conj :x) y (swap! log conj :y1 :y2)] (adopt! y) :ok))))
    (is (= [:y1 :y2] (k! s '(deref log))) "only the adopted branch's intents ran")
    (k! s '(fork [x (swap! log conj :never)] :ok))
    (is (= [:y1 :y2] (k! s '(deref log))) "a discarded branch's intents are dropped")
    (is (instance? klara.authority.Intent (first (k! s '(fork [x (swap! log conj :z)])))))
    (testing "the branch does not observe its own deferred effect"
      (is (= [[:y1 :y2]] (k! s '(fork [x (do (swap! log conj :q) (deref log))])))))
    (testing "nested forks: intents reach the outermost adoption"
      (k! s '(fork [o (fork [i (swap! log conj :inner)] (adopt! i) :i)] :not-adopted))
      (is (= [:y1 :y2] (k! s '(deref log))))
      (k! s '(fork [o (fork [i (swap! log conj :inner)] (adopt! i) :i)] (adopt! o)))
      (is (= [:y1 :y2 :inner] (k! s '(deref log)))))
    (testing "intents keep their order and leave receipts"
      (k! s '(fork [x (do (swap! log conj 1) (swap! log conj 2) (swap! log conj 3))] (adopt! x)))
      (is (= [1 2 3] (subvec (k! s '(deref log)) 3)))
      (is (= 3 (count (filter #(and (= :intent (:kind %)) (= 0 (:branch %)))
                              (take-last 3 (k! s '(receipts))))))))
    (testing "acting directly needs a capability, transferred to exactly one branch"
      (k! s '(def cap (capability :io)))
      (k! s '(fork {:transfer {cap 0}} [x (direct cap (swap! log conj :now)) y 1] :discarded))
      (is (= :now (peek (k! s '(deref log)))) "ran at once, though the branch was discarded")
      (is (= {:kind :direct :op 'clojure.core/swap!} (select-keys (peek (k! s '(receipts))) [:kind :op])))
      (is (re-find #"not transferred" (err s '(fork {:transfer {cap 0}} [x 1 y (direct cap (swap! log conj :no))]))))
      (is (re-find #"needs a capability" (err s '(direct (resource 1) (swap! log conj :no)))))
      (is (= 2 (k! s '(do (direct cap (swap! log conj :top)) 2))) "outside forks it runs too, with a receipt"))
    (testing "a failing intent leaves the adoption :incomplete, later intents unrun"
      (is (re-find #"adoption incomplete: intent 2 of 3"
                   (err s '(fork [x (do (swap! log conj :a) (reset! 42 0) (swap! log conj :c))] (adopt! x)))))
      (is (= :a (peek (k! s '(deref log))))))))
