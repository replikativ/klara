(ns klara.compiler.recipes
  "Optimization recipes written in Klara (design/02-compilation.md, layer L5).

  A recipe is an untrusted function from reference code to candidate code.
  Nothing here needs to be correct for Klara to be safe: the kernel checks
  every candidate against its reference. A recipe only needs to be useful."
  (:require [klara.code :as code]
            [klara.stage :refer [lift]]))

(defn- view-op [c] (:op (code/view c)))

(defn- constant? [c] (= :const (view-op c)))

(defn- value? [c] (contains? #{:const :local :fn :host} (view-op c)))

(defn- plain?
  "Plain data: what folding may produce (no lazy sequences, functions or
   mutable objects)."
  [x]
  (cond (or (nil? x) (number? x) (boolean? x) (string? x) (keyword? x) (symbol? x) (char? x)) true
        (map? x) (every? (fn [[k v]] (and (plain? k) (plain? v))) x)
        (or (vector? x) (set? x)) (every? plain? x)
        :else false))

(defn- fold
  "A pure host function (the checker's table, L4.check.prim) applied to
   constants, evaluated now; nil if it fails or yields something that is not
   plain data."
  [f args]
  (when (code/pure-host? f)
    (let [hf (code/host-fn f)]
      (try (let [r (apply hf (map (fn [a] (:value (code/view a))) args))]
             (when (plain? r) (lift r)))
           (catch Exception _ nil)))))

(defn- recurs-to?
  "Does c contain a recur to `self`, not looking inside other functions?"
  [c self]
  (let [v (code/view c)]
    (or (and (= :recur (:op v)) (= self (:target v)))
        (and (not= :fn (:op v)) (boolean (some #(recurs-to? % self) (code/children c)))))))

(declare inline*)

(defn- inline-app [v depth]
  (let [f (inline* (:fn v) depth)
        args (mapv (fn [a] (inline* a depth)) (:args v))
        fv (code/view f)]
    (cond
      ;; constant folding of host functions
      (and (= :host (:op fv)) (every? constant? args))
      (or (fold f args) (code/make (assoc v :fn f :args args)))

      ;; beta reduction: arguments become lets, in order (L4.check.let-app),
      ;; and the let rule substitutes those that are values; a loop is not
      ;; unrolled (its recur needs the function)
      (and (= :fn (:op fv)) (= (count (:params fv)) (count args))
           (not (and (:self fv) (recurs-to? (:body fv) (:self fv)))))
      (inline* (reduce (fn [body [p a]] (code/make {:op :let :name p :init a :body body}))
                       (if (:self fv) (code/subst (:body fv) {(:self fv) f}) (:body fv))
                       (reverse (map vector (:params fv) args)))
               depth)

      ;; unfold a definition when some argument is known
      (and (pos? depth) (some constant? args) (code/unfold f))
      (inline* (code/make (assoc v :fn (code/unfold f) :args args)) (dec depth))

      :else (code/make (assoc v :fn f :args args)))))

(defn- inline* [c depth]
  (let [v (code/view c)]
    (case (:op v)
      ;; a data definition is its value (L4.check.delta-data)
      :global (or (code/known c) c)
      :app (inline-app v depth)
      :if (let [test (inline* (:test v) depth)]
            (if (constant? test)
              (inline* (if (:value (code/view test)) (:then v) (:else v)) depth)
              (code/make (assoc v :test test :then (inline* (:then v) depth) :else (inline* (:else v) depth)))))
      :let (let [init (inline* (:init v) depth)]
             (if (value? init)
               (inline* (code/subst (:body v) {(:name v) init}) depth)
               (code/make (assoc v :init init :body (inline* (:body v) depth)))))
      :do (code/make (assoc v :body (mapv (fn [b] (inline* b depth)) (:body v))))
      :fn (code/make (assoc v :body (inline* (:body v) depth)))
      c)))

(defn inline
  "Online partial evaluation: fold pure host functions on constants, read
   data definitions, reduce known calls, and unfold definitions called with
   at least one known argument, up to `depth` nested unfoldings (default
   32). The only partial evaluator; klara.jit/simplify is this."
  ([reference] (inline reference 32))
  ([reference depth] (inline* reference depth)))
