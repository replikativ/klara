(ns klara.own
  "Functional but in place, as a specializer (design/04-ownership.md).

  (own/in-place ctx default) rewrites loops whose accumulator is only ever
  replaced by a persistent update of itself: the accumulator starts as a
  transient, the updates become their owned versions (assoc -> assoc!), and
  the exits that return it return (persistent! acc). It is optimistic: the
  kernel admits the candidate only if the ownership judgment holds and the
  erasure means the reference (L4.check.in-place), so compile with
  {:certificate {:kind :in-place}}. Plain Klara over Code views."
  (:require [klara.code :as code]))

(def owned-update
  '{clojure.core/conj klara.core/conj!, clojure.core/assoc klara.core/assoc!,
    clojure.core/dissoc klara.core/dissoc!, clojure.core/disj klara.core/disj!})

(defn- host [q] (code/make {:op :host :name q}))
(defn- app [f args] (code/make {:op :app :fn f :args args}))

(defn- local? [c p] (let [v (code/view c)] (and (= :local (:op v)) (= p (:name v)))))

(defn- update-chain?
  "c is p, or a persistent update whose first argument is an update chain of p."
  [c p]
  (or (local? c p)
      (let [v (code/view c)]
        (and (= :app (:op v))
             (let [f (code/view (:fn v))]
               (and (= :host (:op f)) (contains? owned-update (:name f))
                    (update-chain? (first (:args v)) p)))))))

(defn- own-chain
  "The owned version of an update chain of p."
  [c p]
  (if (local? c p)
    c
    (let [v (code/view c)
          f (code/view (:fn v))]
      (app (host (get owned-update (:name f)))
           (cons (own-chain (first (:args v)) p) (rest (:args v)))))))

(defn- recurs
  "The recurs to `self` in c, not looking inside functions."
  [c self]
  (let [v (code/view c)]
    (cond (= :fn (:op v)) []
          (and (= :recur (:op v)) (= self (:target v))) [v]
          :else (mapcat #(recurs % self) (code/children c)))))

(defn- rewrite-tails
  "Rebuild loop body c: recurs to self get their j-th argument owned, exits
   returning p return (persistent! p)."
  [c p self j]
  (let [v (code/view c)]
    (case (:op v)
      :if (code/make (assoc v :then (rewrite-tails (:then v) p self j) :else (rewrite-tails (:else v) p self j)))
      :let (code/make (assoc v :body (rewrite-tails (:body v) p self j)))
      :do (code/make (assoc v :body (conj (vec (butlast (:body v))) (rewrite-tails (last (:body v)) p self j))))
      :recur (if (= self (:target v))
               (code/make (assoc v :args (assoc (vec (:args v)) j (own-chain (nth (:args v) j) p))))
               c)
      (if (local? c p) (app (host 'klara.core/persistent!) [c]) c))))

(defn- own-loop
  "If c is a loop with an accumulator to own, the rewritten loop, else nil."
  [c]
  (let [v (code/view c)
        f (when (= :app (:op v)) (code/view (:fn v)))]
    (when (and f (= :fn (:op f)) (:self f))
      (let [rs (recurs (:body f) (:self f))
            j (first (filter (fn [j] (let [p (nth (:params f) j)]
                                       (and (seq rs)
                                            (every? #(update-chain? (nth (:args %) j) p) rs)
                                            (some #(not (local? (nth (:args %) j) p)) rs))))
                             (range (count (:params f)))))]
        (when j
          (let [p (nth (:params f) j)]
            (app (code/make (assoc f :body (rewrite-tails (:body f) p (:self f) j)))
                 (assoc (vec (:args v)) j (app (host 'clojure.core/transient) [(nth (:args v) j)])))))))))

(defn rewrite
  "Every loop in c with an accumulator to own, rewritten."
  [c]
  (or (own-loop c)
      (let [cs (code/children c)]
        (if (seq cs) (code/with-children c (mapv rewrite cs)) c))))

(defn in-place
  "The specializer: own the accumulators of the definition's loops."
  [ctx default]
  (rewrite (:reference ctx)))
