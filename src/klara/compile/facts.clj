(ns klara.compile.facts
  "Facts about definitions (design/06-speculation.md#3-facts), computed by
  the kernel's own analyses. The first is purity (L4.facts.pure): calling the
  definition on data cannot mutate anything that existed before the call or
  perform an effect, so running it to measure it (the investor) changes
  nothing but time. Conservative: what the analysis cannot see through is
  not pure."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w]))

(def ^:private allocating
  "Host functions that return a fresh object (mutable or not)."
  '#{clojure.core/boolean-array clojure.core/byte-array clojure.core/char-array
     clojure.core/short-array clojure.core/int-array clojure.core/long-array
     clojure.core/float-array clojure.core/double-array clojure.core/object-array
     clojure.core/make-array clojure.core/ex-info clojure.core/with-meta clojure.core/meta})

(def ^:private array-writes
  '#{clojure.core/aset clojure.core/aset-int clojure.core/aset-long clojure.core/aset-double
     clojure.core/aset-boolean clojure.core/aset-byte clojure.core/aset-char clojure.core/aset-short
     clojure.core/aset-float})

(def ^:private reads
  "Host functions that read objects without changing them."
  '#{clojure.core/aget clojure.core/alength})

(defn- pure-host? [q]
  (or (and (= "clojure.core" (namespace q)) (contains? b/pure-host (symbol (name q))))
      (contains? allocating q)
      (contains? reads q)
      (:pure (b/lookup q))
      ;; Klara's owned operations act persistently outside owned compiled code
      (contains? '#{klara.core/conj! klara.core/assoc! klara.core/dissoc! klara.core/disj!
                    klara.core/pop! klara.core/persistent! klara.core/transient klara.core/own} q)))

(declare definition-pure)

(defn- term-impurity
  "Why term t is not pure, or nil. `fresh` holds locals bound to objects
   allocated in this call (arrays it may write)."
  [ctx t fresh]
  (let [go #(term-impurity ctx % fresh)]
    (case (:op t)
      (:const :local :host) nil
      :global (let [q (get-in t [:link :name])
                    d (w/lookup (:world ctx) q)]
                (when (v/closure? (:value d)) (definition-pure ctx q)))
      :fn (some (fn [a] (term-impurity ctx (:body a) #{})) (:arities t))
      :let (or (go (:init t))
               (term-impurity ctx (:body t)
                              (cond-> fresh
                                (and (= :app (:op (:init t))) (= :host (get-in t [:init :fn :op]))
                                     (contains? allocating (get-in t [:init :fn :name])))
                                (conj (:name t)))))
      :app (let [f (:fn t)]
             (or (case (:op f)
                   :host (let [q (:name f)]
                           (cond (pure-host? q) nil
                                 (and (contains? array-writes q)
                                      (= :local (get-in t [:args 0 :op]))
                                      (contains? fresh (get-in t [:args 0 :name]))) nil
                                 :else (str "calls " q)))
                   (go f))
                 (some go (:args t))))
      (:if :do :recur :throw :try) (some go (t/children t))
      (str "contains " (name (:op t))))))

(defn- definition-pure
  "Why definition q is not pure, or nil; recursive definitions are assumed
   pure while being analysed."
  [ctx q]
  (if (contains? @(:seen ctx) q)
    nil
    (do (vswap! (:seen ctx) conj q)
        (let [d (w/lookup (:world ctx) q)]
          (vswap! (:premises ctx) conj [q (:generation d)])
          (when-let [why (term-impurity ctx (.-term ^klara.runtime.value.Closure (:value d)) #{})]
            (str (t/base-name q) " " why))))))

(defn pure
  "L4.facts.pure: {:pure true :premises #{[q g] ..}} if the function
   definition q is pure in `world`, else {:pure false :why reason}."
  [world q]
  (let [ctx {:world world :seen (volatile! #{}) :premises (volatile! #{})}
        d (w/lookup world q)]
    (if-not (and d (v/closure? (:value d)))
      {:pure false :why (str q " is not a function definition")}
      (if-let [why (definition-pure ctx q)]
        {:pure false :why why}
        {:pure true :premises @(:premises ctx)}))))
