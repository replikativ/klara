(ns klara.compile.updates
  "Checked scalar snapshot updates for privately represented Long vectors.
   All RHSs observe the original snapshot; stores occur only after evaluation.
   This is a tested representation checker, not a kernel theorem."
  (:require [klara.compile.analysis :as analysis]
            [klara.core :as c]))

(defn expression-type [t env]
  (case (:op t)
    :local (get env (- (count env) 1 (:index t)))
    :quote (cond (instance? Long (:datum t)) :long (boolean? (:datum t)) :boolean
                 (and (= clojure.lang.PersistentVector (class (:datum t)))
                      (every? #(instance? Long %) (:datum t))) :long-vector)
    :let (when-let [init (expression-type (:init t) env)]
           (expression-type (:body t) (conj env init)))
    :prim (let [ts (mapv #(expression-type % env) (:args t))]
            (case (:name t)
              nth (when (and (= 2 (count ts)) (= :long-vector (first ts)) (#{:long :int} (second ts))) :long)
              count (when (= ts [:long-vector]) :int)
              (analysis/scalar-result (:name t) ts)))
    nil))

(defn plan
  "Accept an assoc chain rooted at callback parameter 0. RHS scalar reads of
   that parameter must use an in-bounds literal slot. Captured values require
   independently established layouts. Intermediate vector versions cannot
   escape or be read by a subsequent RHS."
  [f length outer-types]
  (when (and (= :fn (:op f)) (= 1 (:arity f)) (not (:rest? f)))
    (let [types (conj (vec outer-types) :long-vector)]
      (letfn [(scalar [t env depth]
                (case (:op t)
                  :local (let [ty (expression-type t env)]
                           (when (and (not= depth (:index t)) (#{:long :int :boolean} ty)) ty))
                  :quote (expression-type t env)
                  :let (when-let [ty (scalar (:init t) env depth)]
                         (when (#{:long :int :boolean} ty)
                           (scalar (:body t) (conj env ty) (inc depth))))
                  :prim
                  (let [as (:args t) child #(scalar % env depth)]
                    (case (:name t)
                      nth (when (and (= 2 (count as)) (#{:long :int} (child (second as))))
                            (if (= (c/local depth) (first as))
                              (let [i (:datum (second as))]
                                (when (and (= :quote (:op (second as))) (instance? Long i) (<= 0 i) (< i length)) :long))
                              (when (= :long-vector (expression-type (first as) env)) :long)))
                      count (when (and (= 1 (count as))
                                       (= :long-vector (expression-type (first as) env))) :int)
                      (analysis/scalar-result (:name t) (mapv child as))))
                  nil))
              (updates [t]
                (if (= (c/local 0) t) []
                  (when (and (= :prim (:op t)) (= 'assoc (:name t)) (= 3 (count (:args t))))
                    (let [[base slot rhs] (:args t) i (:datum slot) previous (updates base)]
                      (when (and (some? previous) (= :quote (:op slot))
                                 (instance? Long i) (<= 0 i) (< i length)
                                 (= :long (scalar rhs types 0)))
                        (conj previous {:index i :rhs rhs}))))))]
        (when-let [writes (updates (:body f))]
          (when (seq writes) {:writes writes :reads :original-snapshot :stores :after-all-rhs}))))))

(defn plans
  "Recover lexical layouts at each owned update. Loop argument layouts come
   from its actual entry; top parameters use explicit admission layouts."
  [term parameter-layouts]
  (let [out (atom {}) invalid-loops (atom [])]
    (letfn [(layout [t env]
              (or (expression-type t env)
                  (when (and (= :perform (:op t)) (= :own/alloc (:name t)))
                    (let [v (:datum (first (:args t)))]
                      (when (and (vector? v) (seq v) (every? #(instance? Long %) v))
                        {:owned (count v)})))))
            (go [t env path]
              (case (:op t)
                :fn (go (:body t) (into env (if (empty? path) parameter-layouts (repeat (:arity t) nil)))
                        (conj path :body))
                :let (do (go (:init t) env (conj path :init))
                         (go (:body t) (conj env (layout (:init t) env)) (conj path :body)))
                :letrec (let [base (into env (repeat (count (:inits t)) nil))
                              ts (mapv #(layout % base) (get-in t [:body :args]))
                              e (conj env {:loop-types ts :path path})]
                          (doseq [[i f] (map-indexed vector (:inits t))]
                            (go (:body f) (into e ts) (conj path :inits i :body))))
                :app (when-let [loop-info (layout (:fn t) env)]
                       (when (and (:loop-types loop-info)
                                  (not= (:loop-types loop-info) (mapv #(layout % env) (:args t))))
                         (swap! invalid-loops conj (:path loop-info))))
                :if (doseq [key [:test :then :else]] (go (get t key) env (conj path key)))
                :perform (when (= :own/update (:name t))
                           (let [[cell f] (:args t) n (:owned (layout cell env))]
                             (when (and n (= 2 (count (:args t))))
                               (when-let [p (plan f n env)] (swap! out assoc path p)))))
                nil))]
      (go term [] [])
      (into {} (remove (fn [[path _]]
                         (some #(= % (subvec path 0 (min (count %) (count path)))) @invalid-loops))) @out))))
