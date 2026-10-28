(ns klara.compile.escape
  "K1 -> K1 plus per-binding alias/use/escape evidence. Adapted from
  raster.analysis.memory (Apache-2.0): track aliases, uses and escape.
  Unlike the source, unknown, host and higher-order calls escape ALL
  their arguments. Replacement is all-or-nothing; every use must be a
  recognized projection or direct local closure call. Preserve initializer
  order, including unused fields and exceptions. No partial escape analysis."
  (:require [clojure.set :as set]
            [klara.compile.ir :as ir] [klara.core :as c]))

(defn alias-closure
  "Bidirectional transitive aliases, ported from raster memory analysis."
  [names aliases]
  (loop [result (set names)]
    (let [next (into result (mapcat #(get aliases % #{}) result))]
      (if (= result next) result (recur next)))))

(defn track-aliases [aliases name direct]
  (let [all (alias-closure direct aliases)]
    (reduce (fn [m other] (update m other (fnil conj #{}) name))
            (assoc aliases name all) all)))

(defn local-names [t]
  (into #{} (keep #(when (= :local (:op %)) (:name %))) (ir/nodes t)))

(defn analyze-let
  "Forward alias closure and backward may-use sets for a sequential let
  spine. Uses in nested functions count as live. last-use? means no alias
  can be read after this initializer; it does not license moving effects."
  [t]
  (let [[bindings body] (loop [t t bs []]
                          (if (= :let (:op t))
                            (recur (:body t) (conj bs [(:name t) (:init t)])) [bs t]))
        aliases (reduce (fn [m [s init]]
                          (track-aliases m s (if (= :local (:op init)) #{(:name init)} #{})))
                        {} bindings)
        used-after (loop [i (dec (count bindings)) live (local-names body) result {}]
                     (if (neg? i) result
                         (let [[s init] (nth bindings i)]
                           (recur (dec i) (set/union (disj live s) (local-names init))
                                  (assoc result s live)))))]
    {:aliases aliases :used-after used-after
     :bindings (mapv (fn [[s _]]
                       (let [as (alias-closure #{s} aliases)]
                         {:binding s :aliases as
                          :last-use? (empty? (set/intersection as (get used-after s)))})) bindings)}))

(defn projection [t s init]
  (when (and (= :prim (:op t)) (= {:op :local :name s} (first (:args t))))
    (let [as (:args t) n (:name t) size (count (:args init))
          i (cond
              (and (= 'first n) (= 1 (count as))) 0
              (and (= 'second n) (= 1 (count as))) 1
              (and (contains? '#{nth get} n) (= 2 (count as)) (= :quote (:op (second as)))) (:datum (second as)))]
      (cond
        (and (= 'vector (:name init)) (integer? i) (<= 0 i) (< i size)) i
        (and (= 'hash-map (:name init)) (= 'get n) (= 2 (count as))
             (= :quote (:op (second as))))
        (last (keep-indexed (fn [j [k _]] (when (= (:datum k) (:datum (second as))) (inc (* 2 j))))
                           (partition 2 (:args init))))))))

(defn analyze [body s init]
  (let [sites (atom []) escapes (atom false)]
    (letfn [(go [t]
              (cond
                (some? (projection t s init)) (swap! sites conj {:kind :projection :term t})
                (and (= :fn (:op init)) (= :app (:op t)) (= {:op :local :name s} (:fn t)))
                (do (swap! sites conj {:kind :call :term t}) (doseq [a (:args t)] (go a)))
                (= {:op :local :name s} t) (reset! escapes true)
                ;; A capture is an escape even when its eventual use looks local.
                (and (= :fn (:op t)) (pos? (ir/uses t s))) (reset! escapes true)
                :else (ir/map-children #(do (go %) %) t)))]
      (go body)
      {:aliases #{s} :use-count (ir/uses body s) :last-use (some-> @sites last :term)
       :escapes? @escapes :sites @sites})))

(defn run [term]
  (let [removed (atom 0) evidence (atom [])]
    (letfn [(go [t]
              (let [t (ir/map-children go t) init (:init t) s (:name t)
                    allocation? (or (= :fn (:op init))
                                    (and (= :prim (:op init))
                                         (or (= 'vector (:name init))
                                             (and (= 'hash-map (:name init))
                                                  (even? (count (:args init)))
                                                  (every? #(and (= :quote (:op %)) (keyword? (:datum %)))
                                                          (take-nth 2 (:args init)))))))]
                (if (and (= :let (:op t)) allocation?)
                  (let [a (analyze (:body t) s init)]
                    (swap! evidence conj (assoc (dissoc a :sites :last-use) :binding s))
                    (if (:escapes? a) t
                        (do (swap! removed inc)
                            (if (= :fn (:op init))
                              (ir/substitute (:body t) {s init})
                              (let [ps (mapv (fn [_] (gensym "field")) (:args init))
                                    replace (fn replace [b]
                                              (if-let [i (projection b s init)]
                                                {:op :local :name (nth ps i)}
                                                (ir/map-children replace b))) ]
                                (reduce (fn [b [p a]] {:op :let :name p :init a :body b})
                                        (replace (:body t)) (reverse (map vector ps (:args init))))))))) t)))]
      {:term (go term) :allocations-removed @removed :bindings @evidence
       :liveness (mapv analyze-let (filter #(= :let (:op %)) (ir/nodes term)))})))
