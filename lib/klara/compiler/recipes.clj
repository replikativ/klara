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

(defn- fold
  "A host function applied to constants, evaluated now; nil if it fails or
   yields something that is not plain data."
  [f args]
  (when-let [hf (code/host-fn f)]
    (try (let [r (apply hf (map (fn [a] (:value (code/view a))) args))]
           (when (or (number? r) (boolean? r) (nil? r) (string? r) (keyword? r))
             (lift r)))
         (catch Exception _ nil))))

(declare inline*)

(defn- inline-app [v depth]
  (let [f (inline* (:fn v) depth)
        args (mapv (fn [a] (inline* a depth)) (:args v))
        fv (code/view f)]
    (cond
      ;; constant folding of host functions
      (and (= :host (:op fv)) (every? constant? args))
      (or (fold f args) (code/make (assoc v :fn f :args args)))

      ;; beta reduction when every argument is a value
      (and (= :fn (:op fv)) (= (count (:params fv)) (count args)) (every? value? args))
      (inline* (code/subst (:body fv)
                           (cond-> (zipmap (:params fv) args)
                             (:self fv) (assoc (:self fv) f)))
               depth)

      ;; unfold a definition when some argument is known
      (and (pos? depth) (some constant? args) (code/unfold f))
      (inline* (code/make (assoc v :fn (code/unfold f) :args args)) (dec depth))

      :else (code/make (assoc v :fn f :args args)))))

(defn- inline* [c depth]
  (let [v (code/view c)]
    (case (:op v)
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
  "Online partial evaluation: fold constants, reduce known calls, and unfold
   definitions called with at least one constant argument, up to `depth`
   nested unfoldings (default 32)."
  ([reference] (inline reference 32))
  ([reference depth] (inline* reference depth)))
