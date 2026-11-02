(ns klara.formal.laws
  "Law-licensed rewrites (L4.check.law): laws proved once by the ansatz
  kernel, and a certifier that admits a rewrite when it is an instance.

  The fusion laws, for any element types and any (abstract) stages:

    Law.foldl-map     foldl f b (map g l)    = foldl (fn [acc x] (f acc (g x))) b l
    Law.foldl-filter  foldl f b (filter p l) = foldl (fn [acc x] (if (p x) (f acc x) acc)) b l

  The certifier (kind :law) rebuilds the fused term from the reference
  (klara.compile.fusion/fuse) and admits the candidate when it is that term
  up to names. Its premises are the stages' purity (L4.facts.pure, at the
  stages' generations), its guard that the argument is a vector. Trusted:
  that Clojure's reduce, map and filter on a finite vector denote the list
  functions the laws are about, and the fused loop's fallback to the
  reference body on any exception (klara.compile.fusion)."
  (:require [ansatz.core :as a]
            [klara.compile.facts :as facts]
            [klara.compile.fusion :as fusion]
            [klara.compile.kernel :as kernel]
            [klara.lang.builtins :as b]))

(when-not (some-> (try (a/env) (catch Exception _ nil)) (.lookup (ansatz.kernel.name/from-string "Nat.add")))
  (a/load-init!))

(a/theorem Law.foldl-map [α :- Type, β :- Type, γ :- Type, f :- (=> γ β γ), g :- (=> α β), l :- (List α)]
  (forall [b :- γ] (= γ (List.foldl f b (List.map g l)) (List.foldl (fn [acc :- γ, x :- α] (f acc (g x))) b l)))
  (induction l)
  (all_goals (intro b))
  (all_goals (simp [List.foldl, List.map]))
  (try (exact (ih_tail _))))

(a/theorem Law.foldl-filter [α :- Type, γ :- Type, f :- (=> γ α γ), p :- (=> α Bool), l :- (List α)]
  (forall [b :- γ] (= γ (List.foldl f b (List.filter p l))
                        (List.foldl (fn [acc :- γ, x :- α] (match (p x) [true (f acc x)] [false acc])) b l)))
  (induction l)
  (all_goals (intro b))
  (all_goals (simp only [List.filter, List.foldl]))
  (cases hp (p head))
  (all_goals (simp only [hp, List.foldl]))
  (all_goals (exact (ih_tail _))))

(def laws ["Law.foldl-map" "Law.foldl-filter"])

(defn- proved? [n] (some? (.lookup ^ansatz.kernel.Env (a/env) (ansatz.kernel.name/from-string n))))

(defn- pure-stage
  "Premises for stage term `s` being pure, or a reason it is not known to be."
  [world s]
  (case (:op s)
    :host (if (or (:pure (b/lookup (:name s))) (@#'facts/pure-host? (:name s)))
            {:premises #{}}
            {:why (str (:name s) " is not a known pure host function")})
    :global (let [q (get-in s [:link :name]) r (facts/pure world q)]
              (if (:pure r) {:premises (:premises r)} {:why (str q " is not pure: " (:why r))}))
    {:why (str "the stage " (pr-str (:op s)) " is not a named function")}))

(defn certify [{:keys [reference candidate world]}]
  (let [canon (fusion/fuse reference)
        {:keys [f init stages]} (when canon (fusion/stages (:body (first (:arities reference)))))
        checks (when canon (map #(pure-stage world %) (cons f (map second stages))))]
    (cond
      (nil? canon) {:result :failed :message "the reference is not a fold of map and filter stages over its argument"}
      (not (fusion/alpha= canon candidate)) {:result :failed :message "the candidate is not the fused fold of the reference"}
      (not (every? proved? laws)) {:result :failed :message "the fusion laws are not in the kernel's environment"}
      (not= :const (:op init)) {:result :failed :message "the initial value must be a constant"}
      (some :why checks) {:result :failed :message (some :why checks)}
      :else {:result :proved :guards [:vector]
             :premises (reduce into #{} (map :premises checks))
             :evidence {:kind :law :laws laws}})))

(kernel/register-certifier! :law certify)
