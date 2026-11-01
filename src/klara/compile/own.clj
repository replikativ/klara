(ns klara.compile.own
  "Functional but in place (design/04-ownership.md, L4.check.in-place).

  An owned candidate uses transients where its reference uses persistent
  collections. It is admitted when

    1. its erasure (transient and persistent! dropped, conj! as conj, ...)
       is definitionally equal to the reference, and
    2. the ownership judgment WO holds: every transient is the initial value
       of a loop parameter, and inside the loop that parameter is used
       linearly. It is read only before it is consumed, consumed only into
       the recur at its own position, never captured by a function, passed
       anywhere else or returned except through persistent!.

  Leaving compiled code freezes owned values (klara.runtime.prims/freeze),
  and Klara's transient operations act persistently on persistent values, so
  a continuation resumed any number of times goes on correctly. The erasure
  theorem about the formal semantics is open (design/04-ownership.md)."
  (:require [klara.lang.term :as t]))

(def consuming
  "Owned updates and their erased, persistent meanings."
  '{klara.core/conj! clojure.core/conj, klara.core/assoc! clojure.core/assoc,
    klara.core/dissoc! clojure.core/dissoc, klara.core/disj! clojure.core/disj,
    klara.core/pop! clojure.core/pop})

(def reading
  "Reads that consume nothing; they work on transients too."
  '#{clojure.core/get clojure.core/count clojure.core/contains? clojure.core/nth})

(defn- host-app? [t qs]
  (and (= :app (:op t)) (= :host (get-in t [:fn :op])) (contains? qs (get-in t [:fn :name]))))

(defn- host-name [t] (get-in t [:fn :name]))

(def ^:private boundary '#{clojure.core/transient klara.core/persistent!})

(defn erase
  "The persistent program an owned candidate means."
  [t]
  (let [t (if (seq (t/children t)) (t/with-children t (mapv erase (t/children t))) t)]
    (cond (and (host-app? t boundary) (= 1 (count (:args t)))) (first (:args t))
          (host-app? t (set (keys consuming))) (assoc-in t [:fn :name] (consuming (host-name t)))
          :else t)))

;; ---------------------------------------------------------------------------
;; The ownership judgment

(defn- mentions? [t p] (contains? (t/free-locals t) p))

(defn- local? [t p] (and (= :local (:op t)) (= p (:name t))))

(defn- reads-only?
  "p occurs in t only as what a read reads, never inside a function."
  [t p]
  (cond (not (mentions? t p)) true
        (= :fn (:op t)) false
        (local? t p) false
        (and (host-app? t reading) (local? (first (:args t)) p))
        (every? #(not (mentions? % p)) (rest (:args t)))
        :else (every? #(reads-only? % p) (t/children t))))

(defn- chain?
  "t is p, or an owned update of a chain, with reads of p only before it."
  [t p]
  (or (local? t p)
      (and (host-app? t (set (keys consuming)))
           (chain? (first (:args t)) p)
           (every? #(reads-only? % p) (rest (:args t))))))

(defn- tail-ok?
  "The loop body `t` uses parameter p (at position j of loop `self`) linearly."
  [t p self j]
  (case (:op t)
    :if (and (reads-only? (:test t) p) (tail-ok? (:then t) p self j) (tail-ok? (:else t) p self j))
    :let (and (reads-only? (:init t) p) (not= p (:name t)) (tail-ok? (:body t) p self j))
    :do (and (every? #(reads-only? % p) (butlast (:body t))) (tail-ok? (last (:body t)) p self j))
    :recur (if (= self (:target t))
             (let [args (:args t)]
               (and (every? #(reads-only? % p) (take j args))
                    (chain? (nth args j) p)
                    (every? #(not (mentions? % p)) (drop (inc j) args))))
             (not (mentions? t p)))
    ;; an exit: it does not mention p, or it is (persistent! p)
    (or (not (mentions? t p))
        (and (host-app? t #{'klara.core/persistent!}) (local? (first (:args t)) p)))))

(defn- owned-params
  "For a loop app t: [[param index] ..] whose initial argument is (transient e)."
  [t]
  (let [f (:fn t)]
    (when (and (= :app (:op t)) (= :fn (:op f)) (:self f) (= 1 (count (:arities f))))
      (keep-indexed (fn [j a] (when (host-app? a #{'clojure.core/transient})
                                [(nth (:params (first (:arities f))) j) j]))
                    (:args t)))))

(defn violation
  "Why `candidate` does not satisfy WO, or nil."
  [candidate]
  (let [nodes (t/nodes candidate)
        owned-inits (set (for [n nodes :when (= :app (:op n)), [_ j] (owned-params n)] (nth (:args n) j)))]
    (or
     ;; every transient is an owned loop init
     (some (fn [n] (when (and (host-app? n #{'clojure.core/transient}) (not (contains? owned-inits n)))
                     "a transient that is not the initial value of a loop parameter"))
           nodes)
     ;; every owned parameter is used linearly in its loop
     (some (fn [n]
             (some (fn [[p j]]
                     (let [f (:fn n)
                           body (:body (first (:arities f)))]
                       (when-not (tail-ok? body p (:self f) j)
                         (str "the owned accumulator " (t/base-name p) " escapes or is used after it is updated"))))
                   (owned-params n)))
           (filter #(= :app (:op %)) nodes))
     ;; owned updates and persistent! only on owned parameters (checked above
     ;; for owned loops; anywhere else they would be unowned mutation)
     (let [owned (set (for [n nodes :when (= :app (:op n)), [p _] (owned-params n)] p))]
       (some (fn [n] (when (and (host-app? n (into #{'klara.core/persistent!} (keys consuming)))
                                (not (some #(local? (first (:args n)) %) owned))
                                (not (host-app? (first (:args n)) (set (keys consuming)))))
                       "an owned update of something that is not an owned accumulator"))
             nodes)))))
