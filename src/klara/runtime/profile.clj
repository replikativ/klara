(ns klara.runtime.profile
  "Profiles as data (spec/L4-compiler.md#profiles): snapshots of the
  interpreter's feedback, references annotated with their profiles for
  specializers (L4.jit.context), and profiles saved for a later run
  (L4.profile.saved)."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.intrinsics :as intr :refer [defintrinsic]]
            [klara.runtime.prepare :as prep]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure Code]))

(set! *warn-on-reflection* true)

(defn- ret [st x] (assoc st :mode :ret :ctl x :env nil))

(def ^:private fail intr/fail)

(def ^:private reify-closure intr/reify-closure)


(defn- node-children [n]
  (let [tg (prep/tag n)]
    (case tg
      4 (map #(.-body ^klara.runtime.prepare.Arity %) (.-arities ^klara.runtime.prepare.Fn n))
      5 (cons (.-f ^klara.runtime.prepare.App n) (.-args ^klara.runtime.prepare.App n))
      6 [(.-init ^klara.runtime.prepare.Let n) (.-body ^klara.runtime.prepare.Let n)]
      7 (concat (.-fns ^klara.runtime.prepare.Letrec n) [(.-body ^klara.runtime.prepare.Letrec n)])
      8 [(.-test ^klara.runtime.prepare.If n) (.-then ^klara.runtime.prepare.If n) (.-else ^klara.runtime.prepare.If n)]
      9 (concat (.-exprs ^klara.runtime.prepare.Do n) [(.-last ^klara.runtime.prepare.Do n)])
      10 (.-args ^klara.runtime.prepare.Recur n)
      11 [(.-ex ^klara.runtime.prepare.Throw n)]
      12 (cons (.-body ^klara.runtime.prepare.Try n) (keep :body (.-catches ^klara.runtime.prepare.Try n)))
      13 (.-args ^klara.runtime.prepare.Interop n)
      14 [(.-init ^klara.runtime.prepare.Def n)]
      15 (.-holes ^klara.runtime.prepare.Code n)
      [])))

(defn- describe-callee [x]
  (cond (v/closure? x) (or (some-> (:self (.-term ^Closure x)) str) :fn)
        (keyword? x) x
        :else (str x)))

(defn profile-snapshot
  "The profile of closure `f`: its entries (argument classes and stable
   values), its calls and its branches, with source positions."
  [^Closure f]
  (let [root (.-node f)
        nodes (tree-seq (comp seq node-children) node-children root)
        pos #(:pos (.sourceTerm ^klara.runtime.prepare.INode %))
        snap #(.snapshot ^klara.runtime.prepare.IProfile %)]
    {:entries (snap (.-profile ^klara.runtime.prepare.Fn root))
     :calls (vec (for [n nodes :when (== 5 (prep/tag n))
                       :let [p (snap (.-profile ^klara.runtime.prepare.App n))]
                       :when (pos? (:count p))]
                   {:pos (pos n) :count (:count p) :callee (describe-callee (:callee p))}))
     :branches (vec (for [n nodes :when (== 8 (prep/tag n))
                          :let [[t e] (:branches (snap (.-profile ^klara.runtime.prepare.If n)))]
                          :when (pos? (+ t e))]
                      {:pos (pos n) :then t :else e}))}))

(defn- keep-root-profile
  "reify rebuilds the function term itself; its profile goes back on it."
  [^Code code p]
  (if p (Code. (assoc (.-term code) :profile p)) code))

(defn annotated-reference
  "Code of closure `f` whose terms carry their profiles under :profile
   (L4.jit.context): a function its entries, a call its count and callee,
   an if its branch counts. Prepared nodes share their terms, so the
   profiles are found by identity."
  [^Closure f]
  (let [root (.-node f)
        by-term (java.util.IdentityHashMap.)
        snap #(.snapshot ^klara.runtime.prepare.IProfile %)]
    (doseq [n (tree-seq (comp seq node-children) node-children root)]
      (case (prep/tag n)
        4 (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n) (snap (.-profile ^klara.runtime.prepare.Fn n)))
        5 (let [p (snap (.-profile ^klara.runtime.prepare.App n))]
            (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n)
                  ;; the callee itself (a specializer may guard on it); annotations
                  ;; are stripped before a candidate is stored
                  {:count (:count p) :callee (:callee p)}))
        8 (let [[a b] (:branches (snap (.-profile ^klara.runtime.prepare.If n)))]
            (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n) {:then a :else b}))
        nil))
    (letfn [(annotate [term]
              (let [cs (t/children term)
                    t' (if (seq cs) (t/with-children term (mapv annotate cs)) term)]
                (if-let [p (.get by-term term)] (assoc t' :profile p) t')))]
      (keep-root-profile (reify-closure f (annotate (.-term f)))
                         (.get by-term (.-term f))))))

;; Saved profiles (L4.profile.saved): profiles as data keyed by the path of
;; child indices from the function's term, for a later run (AOT).

(defn- edn-data? [x]
  (cond (or (nil? x) (boolean? x) (number? x) (string? x) (keyword? x) (symbol? x) (char? x)) true
        (or (vector? x) (set? x) (seq? x)) (every? edn-data? x)
        (map? x) (and (not (record? x)) (every? edn-data? (mapcat identity x)))
        :else false))

(defn- small-data?
  "EDN data of at most 64 scalars: worth saving as a stable value."
  [x]
  (and (edn-data? x)
       (<= (count (filter (complement coll?) (tree-seq coll? seq x))) 64)))

(defn- export-profile [p]
  (cond-> (dissoc p :sample)
    (:classes p) (update :classes (fn [cs] (mapv #(if (class? %) (.getName ^Class %) %) cs)))
    (:stable p) (update :stable (fn [vs] (mapv #(if (and (vector? %) (small-data? (second %))) % :unstable) vs)))
    (contains? p :callee) (update :callee #(if (or (string? %) (keyword? %) (nil? %)) % (str %)))))

(defn- import-profile [p]
  (cond-> p
    (:classes p) (update :classes (fn [cs] (mapv #(if (string? %)
                                                     (try (Class/forName ^String %) (catch Throwable _ :polymorphic))
                                                     %) cs)))))

(defn saved-profile
  "The profile of closure `f` as EDN data: {:source id :paths {path profile}},
   where `source` identifies the definition's source form."
  [^Closure f source]
  (let [paths (transient {})]
    (letfn [(walk [term path]
              (when-let [p (:profile term)] (assoc! paths path (export-profile p)))
              (doseq [[i c] (map-indexed vector (t/children term))] (walk c (conj path i))))]
      (walk (.-term ^Code (annotated-reference f)) []))
    {:source source :paths (persistent! paths)}))

(defn reference-with-profile
  "Code of closure `f` annotated with a saved profile instead of its own."
  [^Closure f saved]
  (let [paths (:paths saved)]
    (letfn [(annotate [term path]
              (let [cs (t/children term)
                    t' (if (seq cs)
                         (t/with-children term (vec (map-indexed (fn [i c] (annotate c (conj path i))) cs)))
                         term)]
                (if-let [p (get paths path)] (assoc t' :profile (import-profile p)) t')))]
      (keep-root-profile (reify-closure f (annotate (.-term f) []))
                         (some-> (get paths []) import-profile)))))

(defn strip-annotations
  "The term without profile annotations."
  [term]
  (let [cs (t/children term)]
    (cond-> (dissoc term :profile)
      (seq cs) (t/with-children (mapv strip-annotations cs)))))

(defintrinsic klara.profile/snapshot [st [f]]                   ; L4.profile.snapshot
  (ret st (cond
            (v/closure? f) (profile-snapshot f)
            (instance? klara.runtime.value.IExecutable f)
            (let [r (:reference (v/-describe f))]
              {:compiled true :reference r})
            :else (fail :L4.profile.snapshot (str "no profile for " (pr-str f))))))

(defintrinsic klara.profile/without [st [thunk]]               ; L4.profile.record
  ;; call thunk without recording profiles, as a job with {:profile false}
  ;; does; only the flag is restored when it returns (a continuation resumed
  ;; elsewhere keeps that context's budget and job)
  (let [dyn (:dyn st)]
    (assoc st :mode :apply :ctl [thunk []] :dyn (assoc dyn :no-profile true)
           :k (conj (:k st) {:f :restore-profile :no-profile (:no-profile dyn)}))))
