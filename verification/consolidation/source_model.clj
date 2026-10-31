(ns consolidation.source-model
  "Direct, structural extraction from original core. Never infer semantics
   from a normalized CodeId alone. This extractor is still a trusted bridge."
  (:require [consolidation.helper-bridge :as h]
            [ansatz.kernel.expr :as e]
            [klara.core :as c]
            [klara.fusion.kernel :as k]))

(defn- decline! [message]
  (throw (ex-info message {:reason :source-model})))
(defn- lookup [env t]
  (when-not (= :local (:op t)) (decline! "expected a local in the source loop interface"))
  (or (get env (- (count env) 1 (:index t))) (decline! "source local is out of scope")))
(defn- push-value [env kind]
  (conj (mapv #(cond-> % (contains? % :formal-index) (update :formal-index inc)) env)
        (assoc kind :formal-index 0)))

(defn extract [source inputs]
  (c/assert-wf! source)
  (when-not (and (= :fn (:op source)) (= 1 (:arity source)) (not (:rest? source)))
    (decline! "source must have one iteration-count argument"))
  (letfn [(step [t env]
            (case (:op t)
              :local (let [v (lookup env t)]
                       (if (contains? v :formal-index)
                         (e/app (k/c "HelperTerm.local") (e/lit-nat (:formal-index v)))
                         (decline! "step observes a value outside its helper environment")))
              :quote (let [v (:datum t)]
                       (if (and (instance? Long v) (<= 0 v))
                         (e/app (k/c "HelperTerm.lit") (e/lit-nat (biginteger v)))
                         (decline! "unsupported source step literal")))
              :let (e/app* (k/c "HelperTerm.let_") (step (:init t) env)
                           (step (:body t) (push-value env {:kind :value})))
              :app (let [target (lookup env (:fn t))]
                     (when-not (and (= :helper (:kind target)) (= 1 (count (:args t))))
                       (decline! "step call lacks a closed unary helper interface"))
                     (e/app* (k/c "HelperTerm.call") (:term target) (step (first (:args t)) env)))
              :if (if (and (= :quote (get-in t [:test :op])) (boolean? (get-in t [:test :datum])))
                    (e/app* (k/c "HelperTerm.branch")
                            (k/c (if (get-in t [:test :datum]) "Bool.true" "Bool.false"))
                            (step (:then t) env) (step (:else t) env))
                    (decline! "source step condition is outside the current proof grammar"))
              :prim (let [args (:args t)]
                      (case [(:name t) (count args)]
                        [vector 1] (e/app (k/c "HelperTerm.box") (step (first args) env))
                        [inc 1] (e/app (k/c "HelperTerm.bump") (step (first args) env))
                        [nth 2] (if (= (c/quote* 0) (second args))
                                  (e/app (k/c "HelperTerm.read") (step (first args) env))
                                  (decline! "source proof only supports slot zero"))
                        [assoc 3] (if (= (c/quote* 0) (second args))
                                    (e/app* (k/c "HelperTerm.put") (step (first args) env) (step (nth args 2) env))
                                    (decline! "source proof only supports slot zero"))
                        (decline! "unsupported source step primitive")))
              (decline! "unsupported effect/control in source step")))
          (recur-step [t env]
            (if (= :let (:op t))
              (let [v (lookup env (:init t))]
                (if (contains? v :formal-index)
                  (e/app* (k/c "HelperTerm.let_") (step (:init t) env)
                          (recur-step (:body t) (push-value env (dissoc v :formal-index))))
                  (recur-step (:body t) (conj env v))))
              (do
                (when-not (and (= :app (:op t)) (= :self (:kind (lookup env (:fn t))))
                               (= 2 (count (:args t)))
                               (= :prim (get-in t [:args 0 :op])) (= 'inc (get-in t [:args 0 :name]))
                               (= 1 (count (get-in t [:args 0 :args])))
                               (= :index (:kind (lookup env (get-in t [:args 0 :args 0])))))
                  (decline! "source backedge is not the proved one-step counted recurrence"))
                (step (get-in t [:args 1]) env))))
          (body-step [t env]
            (if (= :let (:op t))
              (let [v (lookup env (:init t))]
                (if (contains? v :formal-index)
                  (e/app* (k/c "HelperTerm.let_") (step (:init t) env)
                          (body-step (:body t) (push-value env (dissoc v :formal-index))))
                  (body-step (:body t) (conj env v))))
              (do
                (when-not (and (= :if (:op t)) (= :prim (get-in t [:test :op]))
                               (= '< (get-in t [:test :name])) (= 2 (count (get-in t [:test :args])))
                               (= :index (:kind (lookup env (get-in t [:test :args 0]))))
                               (= :count (:kind (lookup env (get-in t [:test :args 1]))))
                               (= :acc (:kind (lookup env (:else t)))))
                  (decline! "source loop test or final observation differs from the proved interface"))
                (recur-step (:then t) env))))
          (prefix [t env path]
            (case (:op t)
              :let
              (let [init (:init t)
                    value (case (:op init)
                            :local (lookup env init)
                            :quote (let [v (:datum init)]
                                     (cond
                                       (instance? Long v) {:kind :constant :value v}
                                       (and (= clojure.lang.PersistentVector (class v)) (= 1 (count v))
                                            (instance? Long (first v)) (<= 0 (first v)))
                                       {:kind :seed :value (first v)}
                                       :else (decline! "unsupported source prefix literal")))
                            :fn {:kind :helper :term (h/reify-body init)}
                            :resolve (let [input (get inputs (:id init))]
                                       (when-not (contains? (set (:read-paths input)) path)
                                         (decline! "source helper read is not a mandatory recorded prefix read"))
                                       {:kind :helper :term (h/reify-body (:source input))})
                            (decline! "source prefix has effects or computations outside the proof interface"))]
                (prefix (:body t) (conj env value) (conj path :body)))
              :letrec
              (let [f (first (:inits t)) entry (:body t) env (conj env {:kind :self})
                    args (:args entry)]
                (when-not (and (= 1 (count (:inits t))) (= :fn (:op f)) (= 2 (:arity f)) (not (:rest? f))
                               (= :app (:op entry)) (= :self (:kind (lookup env (:fn entry)))) (= 2 (count args))
                               (= {:kind :constant :value 0} (lookup env (first args)))
                               (= :seed (:kind (lookup env (second args)))))
                  (decline! "source loop entry is outside the proved counted interface"))
                {:seed (:value (lookup env (second args)))
                 :step (body-step (:body f) (into env [{:kind :index} {:kind :acc :formal-index 0}]))})
              (decline! "expected the source counted loop")))]
    (assoc (prefix (:body source) [{:kind :count}] [:body]) :source-id (c/code-id source))))
