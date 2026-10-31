(ns klara.lang.term
  "Core terms (spec/L0-core.md#core-terms): maps with an :op key.

  Locals carry unique names after expansion, so substitution never
  captures. `:fn` terms record `:free`, the locals their body mentions
  from outside (L0.term.free); closures capture exactly those
  (L0.space.closure)."
  (:require [clojure.set :as set]))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------------------
;; Fresh names

(def ^:private ^java.util.concurrent.atomic.AtomicLong counter (java.util.concurrent.atomic.AtomicLong. 0))

(defn fresh
  "A local name that no other expansion or instantiation produces."
  [base]
  (let [base (-> (str base) (clojure.string/replace #"__\d+$" ""))]
    (symbol (str base "__" (.incrementAndGet counter)))))

(defn base-name [sym]
  (-> (str sym) (clojure.string/replace #"__\d+$" "") symbol))

;; ---------------------------------------------------------------------------
;; Constructors

(defn const [v] {:op :const :value v})
(defn local [n] {:op :local :name n})
(defn late [q] {:op :global :link {:kind :late :name q}})
(defn host [q] {:op :host :name q})
(defn app [f args] {:op :app :fn f :args (vec args)})
(defn let1 [n init body] {:op :let :name n :init init :body body})
(defn if* [t a b] {:op :if :test t :then a :else b})
(defn do* [ts] (if (= 1 (count ts)) (first ts) {:op :do :body (vec ts)}))

(declare free-locals nodes)

(defn arity [params rest body]
  {:params (vec params) :rest rest :body body})

(defn fn-term
  "A closure term. `self` names the function inside its own body (or nil)."
  [self arities]
  (let [bound (fn [{:keys [params rest]}] (cond-> (set params) rest (conj rest)))
        free (reduce set/union #{}
                     (map (fn [a] (set/difference (free-locals (:body a)) (bound a))) arities))
        free (cond-> free self (disj self))]
    {:op :fn :self self :arities (vec arities) :free (vec (sort free))}))

;; ---------------------------------------------------------------------------
;; Children: a uniform view used by every traversal below

(defn children
  "Direct subterms of `t`, in evaluation order."
  [t]
  (case (:op t)
    (:const :local :global :host :hole) []
    :fn (mapv :body (:arities t))
    :app (into [(:fn t)] (:args t))
    :let [(:init t) (:body t)]
    :letrec (conj (mapv second (:bindings t)) (:body t))
    :if [(:test t) (:then t) (:else t)]
    :do (:body t)
    :throw [(:ex t)]
    :try (cond-> (into [(:body t)] (map :body (:catches t)))
           (:finally t) (conj (:finally t)))
    :interop (cond-> (vec (:args t)) (not (:static? t)) (->> (into [(:target t)])))
    :def [(:init t)]
    :perform (into [(:effect t)] (:args t))
    :handle [(:handlers t) (:body t)]
    :code (into [(:template t)] (:holes t))
    :recur (:args t)))

(defn binders
  "Locals bound by `t` itself (not by its subterms)."
  [t]
  (case (:op t)
    :fn (cond-> (set (mapcat (fn [a] (cond-> (:params a) (:rest a) (conj (:rest a))))
                             (:arities t)))
          (:self t) (conj (:self t)))
    :let #{(:name t)}
    :letrec (set (map first (:bindings t)))
    :try (set (map :name (:catches t)))
    #{}))

(defn free-locals
  "Locals occurring free in `t`. Holes of a :code term count; its template
   does not, except for the template's own free locals (cross-stage uses)."
  [t]
  (case (:op t)
    :local #{(:name t)}
    (:const :global :host :hole) #{}
    :fn (set (:free t))
    :let (set/union (free-locals (:init t)) (disj (free-locals (:body t)) (:name t)))
    :letrec (set/difference (reduce set/union (map free-locals (children t))) (binders t))
    :try (set/union (free-locals (:body t))
                    (reduce set/union #{} (map (fn [c] (disj (free-locals (:body c)) (:name c)))
                                               (:catches t)))
                    (if (:finally t) (free-locals (:finally t)) #{}))
    ;; holes see the template's binders as future-stage variables, not as free locals
    :code (let [bound (into #{} (mapcat binders) (nodes (:template t)))]
            (set/union (set (:free t))
                       (set/difference (reduce set/union #{} (map free-locals (:holes t))) bound)))
    (reduce set/union #{} (map free-locals (children t)))))

(defn globals
  "Qualified names of late, pinned and guarded links in `t`."
  [t]
  (into #{} (comp (filter #(= :global (:op %))) (map #(get-in % [:link :name])))
        (tree-seq (comp seq children) children t)))

(defn nodes [t] (tree-seq (comp seq children) children t))

;; ---------------------------------------------------------------------------
;; Rebuilding with new children (used by renaming and substitution)

(defn with-children
  "`t` with its children replaced by `cs` (same order as `children`)."
  [t cs]
  (let [cs (vec cs)]
    (case (:op t)
      (:const :local :global :host :hole) t
      :fn (assoc t :arities (mapv (fn [a b] (assoc a :body b)) (:arities t) cs))
      :app (assoc t :fn (first cs) :args (subvec cs 1))
      :let (assoc t :init (cs 0) :body (cs 1))
      :letrec (assoc t :bindings (mapv (fn [[n _] i] [n i]) (:bindings t) (pop cs)) :body (peek cs))
      :if (assoc t :test (cs 0) :then (cs 1) :else (cs 2))
      :do (assoc t :body cs)
      :throw (assoc t :ex (cs 0))
      :try (let [n (count (:catches t))]
             (cond-> (assoc t :body (cs 0)
                            :catches (mapv (fn [c b] (assoc c :body b)) (:catches t) (subvec cs 1 (inc n))))
               (:finally t) (assoc :finally (cs (inc n)))))
      :interop (if (:static? t) (assoc t :args cs) (assoc t :target (first cs) :args (subvec cs 1)))
      :def (assoc t :init (cs 0))
      :perform (assoc t :effect (first cs) :args (subvec cs 1))
      :handle (assoc t :handlers (cs 0) :body (cs 1))
      :code (assoc t :template (first cs) :holes (subvec cs 1))
      :recur (assoc t :args cs))))

(defn refresh-free
  "Recompute :free of every :fn term bottom-up (after splicing or substitution)."
  [t]
  (let [t (with-children t (map refresh-free (children t)))]
    (if (= :fn (:op t)) (fn-term (:self t) (:arities t)) t)))

(defn rename
  "Rename locals according to `m` everywhere (binders and uses). Names not
   in `m` are kept. Unique names make this capture-free."
  [t m]
  (if (empty? m) t
    (let [r #(get m % %)
          t (with-children t (map #(rename % m) (children t)))]
      (case (:op t)
        :local (update t :name r)
        :fn (-> t (update :self #(some-> % r))
                (update :arities (fn [as] (mapv #(-> % (update :params (partial mapv r))
                                                       (update :rest (fn [x] (some-> x r)))) as)))
                (update :free (partial mapv r)))
        :let (update t :name r)
        :letrec (update t :bindings (partial mapv (fn [[n i]] [(r n) i])))
        :try (update t :catches (partial mapv #(update % :name r)))
        :code (update t :free (partial mapv r))
        t))))

(defn freshen
  "Rename every binder in `t` to a fresh name (for each instantiation of a
   template, L2.code.build). Returns [term renaming]."
  [t]
  (let [bs (into #{} (mapcat binders) (nodes t))
        m (into {} (map (fn [b] [b (fresh b)])) bs)]
    [(rename t m) m]))

(defn substitute
  "Replace free uses of locals by terms: `m` maps name -> term. Binders are
   unique, so no capture check is needed."
  [t m]
  (if (empty? m) t
    (case (:op t)
      :local (get m (:name t) t)
      (let [t' (with-children t (map #(substitute % m) (children t)))]
        (if (= :fn (:op t')) (fn-term (:self t') (:arities t')) t')))))

;; ---------------------------------------------------------------------------
;; Printing (L2.print.form): a readable form. Not read back; Code is not text.

(declare ->form)

(def ^:dynamic *world-name* (fn [w] (str w)))

(defn- literal? [v]
  (or (nil? v) (boolean? v) (number? v) (string? v) (keyword? v) (char? v)
      (and (coll? v) (not (record? v)) (every? literal? (if (map? v) (mapcat identity v) v)))))

(defn- link-form [{:keys [kind name world generation]}]
  (case kind
    :late name
    :pinned (list 'klara/at (symbol (*world-name* world)) name)
    :guarded (list 'klara/guarded name generation)))

(defn- arity-form [{:keys [params rest body]}]
  (list (cond-> (vec params) rest (conj '& rest)) (->form body)))

(defn ->form [t]
  (case (:op t)
    :const (let [v (:value t)]
             (cond (or (symbol? v) (seq? v)) (list 'quote v)
                   (literal? v) v
                   :else (list 'klara/const v)))
    :local (:name t)
    :global (link-form (:link t))
    :host (let [n (:name t)] (if (= "clojure.core" (namespace n)) (symbol (name n)) n))
    :fn (let [as (:arities t)]
          (cond-> (list* 'fn (if (= 1 (count as)) (arity-form (first as)) (map arity-form as)))
            (and (:self t) (not (re-matches #"fn|loop\d+" (str (base-name (:self t))))))
            (as-> f (list* 'fn (:self t) (rest f)))))
    :app (list* (->form (:fn t)) (map ->form (:args t)))
    :let (let [[bs body] (loop [t t bs []]
                           (if (= :let (:op t))
                             (recur (:body t) (conj bs (:name t) (->form (:init t))))
                             [bs t]))]
           (list 'let bs (->form body)))
    :letrec (list 'letfn (mapv (fn [[n f]] (list* n (rest (->form f)))) (:bindings t)) (->form (:body t)))
    :if (list 'if (->form (:test t)) (->form (:then t)) (->form (:else t)))
    :do (list* 'do (map ->form (:body t)))
    :recur (list* 'recur (map ->form (:args t)))
    :throw (list 'throw (->form (:ex t)))
    :try (concat (list 'try (->form (:body t)))
                 (map (fn [c] (list 'catch (symbol (.getName ^Class (:class c))) (:name c) (->form (:body c))))
                      (:catches t))
                 (when (:finally t) [(list 'finally (->form (:finally t)))]))
    :interop (if (:static? t)
               (list* (symbol (.getName ^Class (:target t)) (str (:member t))) (map ->form (:args t)))
               (list* (symbol (str "." (:member t))) (->form (:target t)) (map ->form (:args t))))
    :def (list 'def (:name t) (->form (:init t)))
    :perform (list* 'perform (->form (:effect t)) (map ->form (:args t)))
    :handle (list 'handle (->form (:handlers t)) (->form (:body t)))
    :code (list 'code (->form (:template t)))
    :hole (list 'esc (symbol (str "hole" (:index t))))))
