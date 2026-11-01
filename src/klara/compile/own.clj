(ns klara.compile.own
  "Functional but in place (design/04-ownership.md, L4.check.in-place).

  An owned candidate marks loop accumulators `own` and updates them with
  Klara's owned operations (conj!, assoc!, ...) where its reference uses
  persistent ones. It is admitted when

    1. its erasure (own, transient and persistent! dropped, conj! read as
       conj, ...) is definitionally equal to the reference, and
    2. the ownership judgment WO holds: every `own` is the initial value of a
       parameter of the loop it starts, and inside that loop the parameter is
       used linearly. It is read only before it is consumed, consumed only
       into the recur at its own position, never captured by a function,
       passed anywhere else or returned except through persistent!.

  Only compiled code admitted this way makes real transients (lowering turns
  `own` into `transient`); everywhere else these operations are their
  persistent meanings, and compiled code freezes owned values when it leaves
  (klara.runtime.prims). The erasure theorem about the formal semantics is
  open (design/04-ownership.md)."
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

(def ^:private boundary '#{klara.core/own klara.core/transient klara.core/persistent!})

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

(defn- linear?
  "The loop body `t` uses parameter p (at position j of loop `self`) linearly."
  [t p self j]
  (case (:op t)
    :if (and (reads-only? (:test t) p) (linear? (:then t) p self j) (linear? (:else t) p self j))
    :let (and (reads-only? (:init t) p) (not= p (:name t)) (linear? (:body t) p self j))
    :do (and (every? #(reads-only? % p) (butlast (:body t))) (linear? (last (:body t)) p self j))
    :recur (if (= self (:target t))
             (let [args (:args t)]
               (and (every? #(reads-only? % p) (take j args))
                    (chain? (nth args j) p)
                    (every? #(not (mentions? % p)) (drop (inc j) args))))
             (not (mentions? t p)))
    ;; an exit: it does not mention p, or it is (persistent! p)
    (or (not (mentions? t p))
        (and (host-app? t #{'klara.core/persistent!}) (local? (first (:args t)) p)))))

(defn- owned-positions
  "For a loop app t (a one-arity named function applied where it is made):
   {j param} for the arguments that are (own e)."
  [t]
  (let [f (:fn t)]
    (when (and (= :app (:op t)) (= :fn (:op f)) (:self f) (= 1 (count (:arities f))))
      (into {} (keep-indexed (fn [j a] (when (host-app? a #{'klara.core/own})
                                         [j (nth (:params (first (:arities f))) j)])))
            (:args t)))))

(defn violation
  "Why `candidate` does not satisfy WO, or nil. The judgment follows where
   things are, not what they look like: an `own` is allowed only at the
   initial-value position of an owned loop, checked by its place in the term."
  [candidate]
  (letfn [(walk [t]
            (let [owned (owned-positions t)]
              (cond
                (seq owned)
                (let [f (:fn t)
                      body (:body (first (:arities f)))]
                  (or (some (fn [[j p]]
                              (when-not (linear? body p (:self f) j)
                                (str "the owned accumulator " (t/base-name p)
                                     " escapes or is used after it is updated")))
                            owned)
                      ;; the initial values themselves, the other arguments, the body
                      (some walk (map-indexed (fn [j a] (if (contains? owned j) (first (:args a)) a)) (:args t)))
                      (walk f)))
                (host-app? t #{'klara.core/own})
                "an own that is not the initial value of a loop parameter"
                :else (some walk (t/children t)))))]
    (walk candidate)))
