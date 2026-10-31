(ns consolidation.indexed-binding
  "Indexed lexical renaming model for the actual inline correspondence checker.
   Total expression semantics; ordered failure/effect behavior is covered by
   ordered-call separately. Decoding actual Core remains a tested bridge."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm] [klara.fusion.kernel :as k]))

(def theorem-names ["index-lift-agreement" "index-renaming-preserves-evaluation"])
(defn- build! []
  (binding [*ns* (the-ns 'consolidation.indexed-binding)]
    (reset! a/ansatz-env (k/env*))
    (a/inductive IndexExpr [] (literal [token Nat]) (local [index Nat])
      (combine [left IndexExpr] [right IndexExpr]) (bind [initial IndexExpr] [body IndexExpr]))
    (a/defn indexPush [V :- Type, env :- (=> Nat V), value :- V, i :- Nat] V
      (match i [zero value] [(succ previous) (env previous)]))
    (a/defn indexLift [rename :- (=> Nat Nat), i :- Nat] Nat
      (match i [zero 0] [(succ previous) (Nat.succ (rename previous))]))
    (a/defn indexRename [term :- IndexExpr] (=> (=> Nat Nat) IndexExpr)
      (match term
        [(literal token) (fn [rename :- (=> Nat Nat)] (IndexExpr.literal token))]
        [(local i) (fn [rename :- (=> Nat Nat)] (IndexExpr.local (rename i)))]
        [(combine left right) (fn [rename :- (=> Nat Nat)]
                               (IndexExpr.combine (indexRename left rename) (indexRename right rename)))]
        [(bind initial body) (fn [rename :- (=> Nat Nat)]
                              (IndexExpr.bind (indexRename initial rename) (indexRename body (indexLift rename))))]))
    (a/defn indexEval [V :- Type, term :- IndexExpr]
      (=> (=> Nat V) (=> (=> Nat V) (=> (=> V (=> V V)) V)))
      (match term
        [(literal token) (fn [env :- (=> Nat V), literals :- (=> Nat V), op :- (=> V (=> V V))]
                           (literals token))]
        [(local i) (fn [env :- (=> Nat V), literals :- (=> Nat V), op :- (=> V (=> V V))]
                     (env i))]
        [(combine left right)
         (fn [env :- (=> Nat V), literals :- (=> Nat V), op :- (=> V (=> V V))]
           (op (indexEval V left env literals op) (indexEval V right env literals op)))]
        [(bind initial body)
         (fn [env :- (=> Nat V), literals :- (=> Nat V), op :- (=> V (=> V V))]
           (indexEval V body (indexPush V env (indexEval V initial env literals op)) literals op))]))
    (a/theorem index-lift-agreement
      [V :- Type, rename :- (=> Nat Nat), source :- (=> Nat V), target :- (=> Nat V),
       agreement :- (forall [i :- Nat] (= V (target (rename i)) (source i))), value :- V, i :- Nat]
      (= V (indexPush V target value (indexLift rename i)) (indexPush V source value i))
      (cases i)
      (all_goals (simp only [indexPush.eq_1 indexPush.eq_2 indexLift.eq_1 indexLift.eq_2]))
      (all_goals (try (rfl))) (all_goals (apply agreement)))
    (a/theorem index-renaming-preserves-evaluation [term :- IndexExpr]
      (forall [V :- Type, rename :- (=> Nat Nat), source :- (=> Nat V), target :- (=> Nat V),
               literals :- (=> Nat V), op :- (=> V (=> V V)),
               agreement :- (forall [i :- Nat] (= V (target (rename i)) (source i)))]
        (= V (indexEval V (indexRename term rename) target literals op)
             (indexEval V term source literals op)))
      (induction term)
      (all_goals (intro V) (intro rename) (intro source) (intro target)
                 (intro literals) (intro op) (intro agreement))
      (all_goals (simp only [indexRename.eq_1 indexRename.eq_2 indexRename.eq_3 indexRename.eq_4
                            indexEval.eq_1 indexEval.eq_2 indexEval.eq_3 indexEval.eq_4]))
      (all_goals (try (rfl)))
      (all_goals (try (apply agreement)))
      (all_goals
        (try (exact (Eq.trans
          (congrArg (fn [x :- V] (op x (indexEval V (indexRename right rename) target literals op)))
                    (ih_left V rename source target literals op agreement))
          (congrArg (fn [y :- V] (op (indexEval V left source literals op) y))
                    (ih_right V rename source target literals op agreement))))))
      (all_goals (try (rw [(ih_initial V rename source target literals op agreement)])))
      (all_goals (try (apply ih_body)))
      (all_goals (try (apply index-lift-agreement)))
      (all_goals (exact agreement))))
  @a/ansatz-env)

(defonce proof-state
  (delay (locking a/ansatz-env
           (let [previous @a/ansatz-env]
             (try (binding [*out* (java.io.StringWriter.)] (build!))
                  (finally (reset! a/ansatz-env previous)))))))
(defn verify-theorems! []
  (mapv (fn [name]
          (let [en @proof-state d (env/lookup en (nm/from-string name))
                goal (env/ci-type d) proof (env/ci-value d)
                accepted (env/verifies? en goal proof)
                self-reference (contains? (k/constants-of proof) name)]
            (when-not (and accepted (not self-reference)) (throw (ex-info "indexed binding theorem rejected" {:theorem name})))
            {:theorem name :kernel-accepted accepted :self-reference self-reference
             :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)})) theorem-names))
