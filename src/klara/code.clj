(ns klara.code
  "Code values (doc/guide/05-staging.md): the term language of
  generated code, its free variables, conversion to and from Klara Core,
  and printing as Klara source.

  A CODE VALUE wraps an S-TERM. An s-term has the shape of a core term
  (klara.core) with one difference: variables are NAMES, not de Bruijn
  indices. A binder node carries :names (fn: its parameters, let: one,
  letrec: one per init, handle: the instance) and a variable is
  {:op :var :name g}. Names are `Gen` values, unique for the life of the
  process, so generated binders are fresh by construction (hygiene), and
  splicing a code value under any binder can neither capture nor be
  captured. Index terms cannot be spliced under binders without shifting;
  names make splicing plain substitution of a subtree.

  Open code is code with free names. `s->core` turns closed code into a
  core term (names to indices) and reports any free name as a scope
  extrusion: running open code is a detected error.

  Printing renames: every Gen is shown as base_n, numbered in order of
  first appearance in that printed value, so the printed source does not
  depend on how many names the process has generated before (this keeps
  REPL transcripts stable)."
  (:require [clojure.string :as str]))

;; ---------------------------------------------------------------------------
;; names, code values, code-variable markers
;; ---------------------------------------------------------------------------

(defrecord Gen [base id])

(defonce ^:private counter (atom 0))

(defn fresh
  "A fresh name with display base `base` (a string or symbol)."
  [base]
  (->Gen (let [b (str (or base "x"))] (if (str/blank? b) "x" b))
         (swap! counter inc)))

(deftype Code [term]
  Object
  (toString [_] (str "#<code>")))

(defn code? [x] (instance? Code x))
(defn ->code [t] (Code. t))
(defn code-term [^Code c] (.-term c))

(deftype CodeVar [name level])
(defn code-var? [x] (instance? CodeVar x))
(defn ->code-var [nm level] (CodeVar. nm level))
(defn code-var-name [^CodeVar v] (.-name v))

(defn var-term [nm] {:op :var :name nm})

;; ---------------------------------------------------------------------------
;; structure of s-terms (and core terms: the same shapes, :var vs :local)
;; ---------------------------------------------------------------------------

(defn binder-arity [t]
  (case (:op t)
    :fn (+ (:arity t) (if (:rest? t) 1 0))
    :let 1
    :letrec (count (:inits t))
    :handle 1
    0))

(defn- handle-keys [t] (sort (keys (:clauses t))))

(defn parts
  "Children of term t as [child under-binder?] pairs, in evaluation order."
  [t]
  (case (:op t)
    (:var :local :quote :resolve) []
    :fn [[(:body t) true]]
    :let [[(:init t) false] [(:body t) true]]
    :letrec (conj (mapv (fn [i] [i true]) (:inits t)) [(:body t) true])
    :if [[(:test t) false] [(:then t) false] [(:else t) false]]
    :app (mapv (fn [c] [c false]) (into [(:fn t)] (:args t)))
    (:prim :recur) (mapv (fn [c] [c false]) (:args t))
    :specialize (mapv (fn [c] [c false]) (into [(:fn t)] (:args t)))
    :perform (mapv (fn [c] [c false]) (cond->> (:args t) (:target t) (into [(:target t)])))
    :handle (-> (mapv (fn [k] [(get (:clauses t) k) false]) (handle-keys t))
                (cond-> (:return t) (conj [(:return t) false]))
                (conj [(:body t) true]))
    (:code :esc) [[(:body t) false]]))

(defn reassemble
  "Rebuild node t from new children (in `parts` order) and names."
  [t kids names]
  (let [kids (vec kids)
        base (cond-> (dissoc t :names) (seq names) (assoc :names (vec names)))]
    (case (:op t)
      (:var :local :quote :resolve) base
      :fn (assoc base :body (kids 0))
      :let (assoc base :init (kids 0) :body (kids 1))
      :letrec (assoc base :inits (pop kids) :body (peek kids))
      :if (assoc base :test (kids 0) :then (kids 1) :else (kids 2))
      :app (assoc base :fn (kids 0) :args (subvec kids 1))
      :prim (assoc base :args kids)
      :specialize (assoc base :fn (kids 0) :args (subvec kids 1))
      :perform (if (:target t)
                 (assoc base :target (kids 0) :args (subvec kids 1))
                 (assoc base :args kids))
      :handle (let [ks (handle-keys t) n (count ks)]
                (assoc base
                       :clauses (zipmap ks (subvec kids 0 n))
                       :return (when (:return t) (kids n))
                       :body (peek kids)))
      (:code :esc) (assoc base :body (kids 0)))))

(defn free-vars
  "Free names of s-term t."
  ([t] (free-vars t #{}))
  ([t bound]
   (if (= :var (:op t))
     (if (contains? bound (:name t)) #{} #{(:name t)})
     (let [inner (into bound (:names t))]
       (reduce (fn [acc [c under?]] (into acc (free-vars c (if under? inner bound))))
               #{} (parts t))))))

(defn size
  "Number of nodes of an s-term (or core term)."
  [t]
  (reduce + 1 (map (comp size first) (parts t))))

(defn code-size
  "Number of nodes of a code value's term: the size measure used to
  compare generators (e.g. with and without let-insertion)."
  [c]
  (when-not (code? c)
    (throw (ex-info "code-size expects a code value" {:klara/error :stage :value c})))
  (size (code-term c)))

(defn code-vector
  "The code of a vector whose elements are the given code values: an
  n-ary splice for an n known only at generation time. The elements'
  free names are checked when the result is spliced or run."
  [cs]
  (when-not (every? code? cs)
    (throw (ex-info "code-vector expects code values" {:klara/error :stage})))
  (->code {:op :prim :name 'vector :args (mapv code-term cs)}))

(defn closed? "A code value without free names." [c]
  (and (code? c) (empty? (free-vars (code-term c)))))

;; ---------------------------------------------------------------------------
;; s-term <-> core term
;; ---------------------------------------------------------------------------

(defn extrusion-error
  "The scope-extrusion error for name g (BER MetaOCaml's dynamic check)."
  [g what]
  (ex-info (str "code mentions " (:base g) ", whose binder is not in scope " what
                " (a variable escaped the code that binds it)")
           {:klara/error :scope-extrusion :name g}))

(defn s->core
  "Closed s-term -> core term. A free name is a scope-extrusion error."
  ([t] (s->core t []))
  ([t stack]
   (if (= :var (:op t))
     (let [i (.lastIndexOf ^java.util.List stack (:name t))]
       (when (neg? i) (throw (extrusion-error (:name t) "where the code is run")))
       {:op :local :index (- (count stack) 1 i)})
     (let [ns (:names t)
           inner (into stack ns)
           kids (map (fn [[c under?]] (s->core c (if under? inner stack))) (parts t))
           out (reassemble t kids nil)]
       (if (seq ns)
         (with-meta out {:klara/names (mapv (comp symbol :base) ns)})
         out)))))

(defn binder-bases [t n]
  (let [ns (:klara/names (meta t))]
    (mapv (fn [i] (or (some-> (get ns i) name) (if (= :handle (:op t)) "h" "x"))) (range n))))

(defn- core->s* [t stack resolve-free]
  (if (= :local (:op t))
    (let [i (:index t) n (count stack)]
      (if (< i n)
        (var-term (nth stack (- n 1 i)))
        (resolve-free (- i n))))
    (let [k (binder-arity t)
          ns (mapv fresh (binder-bases t k))
          inner (into stack ns)
          kids (map (fn [[c under?]] (core->s* c (if under? inner stack) resolve-free)) (parts t))]
      (reassemble t kids ns))))

(defn core->s
  "Core term -> s-term with fresh names. resolve-free maps an index that
  points past the term's own binders (0 = innermost free slot) to an
  s-term; by default free indices are an error."
  ([t] (core->s t (fn [i] (throw (ex-info "core->s: free local" {:index i})))))
  ([t resolve-free] (core->s* t [] resolve-free)))

;; ---------------------------------------------------------------------------
;; printing as Klara source
;; ---------------------------------------------------------------------------

(defn- needs-quote? [d]
  (some #(or (symbol? %) (seq? %)) (tree-seq coll? seq d)))

(defn- literal [d]
  (cond
    (and (or (symbol? d) (seq? d) (coll? d)) (needs-quote? d)) (list 'quote d)
    :else d))

(defn- host-name [sym]
  (if (and (= "clojure.core" (namespace sym))
           (= (ns-resolve (the-ns 'clojure.core) (symbol (name sym)))
              (resolve sym)))
    (symbol (name sym))
    sym))

(defn- quoted-sym [t] (when (and (= :quote (:op t)) (symbol? (:datum t))) (:datum t)))

(declare ->form binder-name)

(defn- name-of [rn g]
  (or (get @rn g)
      (let [s (symbol (str (:base g) "_" (inc (count @rn))))]
        (swap! rn assoc g s)
        s)))

(defn- binder-name [rn g body]
  (if (and (= "_" (:base g)) (not (contains? (free-vars body) g)))
    '_
    (name-of rn g)))

(defn- let-chain [t rn]
  (loop [t t binds []]
    (if (= :let (:op t))
      (let [g (first (:names t))
            init (->form (:init t) rn)]
        (recur (:body t) (conj binds [(binder-name rn g (:body t)) init])))
      (if (every? #(= '_ (first %)) binds)
        (let [body (->form t rn)
              body (if (and (seq? body) (= 'do (first body))) (rest body) [body])]
          (apply list 'do (concat (map second binds) body)))
        (list 'let (vec (mapcat identity binds)) (->form t rn))))))

(defn- params [t rn]
  (let [ns (mapv #(binder-name rn % (:body t)) (:names t))]
    (if (:rest? t)
      (conj (pop ns) '& (peek ns))
      ns)))

(defn- fn-form [t rn] (list 'fn (params t rn) (->form (:body t) rn)))

(defn- perform-form [t rn]
  (let [args (:args t) op (:name t)
        f #(->form % rn)]
    (cond
      (:target t) (apply list 'perform (f (:target t)) op (map f args))
      (and (= :host/call op) (quoted-sym (first args)))
      (apply list (host-name (quoted-sym (first args))) (map f (rest args)))
      (and (= :host/var op) (quoted-sym (first args)))
      (host-name (quoted-sym (first args)))
      (and (= :host/static op) (quoted-sym (first args)) (quoted-sym (second args)))
      (apply list (symbol (str (quoted-sym (first args))) (str (quoted-sym (second args))))
             (map f (drop 2 args)))
      (and (= :host/static-field op) (quoted-sym (first args)) (quoted-sym (second args)))
      (symbol (str (quoted-sym (first args))) (str (quoted-sym (second args))))
      (= :exn/raise op) (list 'throw (f (first args)))
      (and (#{:stage/run :stage/lift :stage/genlet} op) (= 1 (count args)))
      (list (symbol (name op)) (f (first args)))
      (and (= :stage/locus-rec op) (= :fn (:op (first args))) (= 1 (:arity (first args))))
      (let [lam (first args)]
        (list 'with-genletrec [(name-of rn (first (:names lam)))] (f (:body lam))))
      :else (apply list 'perform op (map f args)))))

(defn- self-var? [t h] (and (= :var (:op t)) (= h (:name t))))

(defn- tail-only?
  "Does name h occur in t only as the operator of calls in tail position?"
  [t h tail?]
  (cond
    (self-var? t h) false
    (and (= :app (:op t)) (self-var? (:fn t) h))
    (and tail? (not-any? #(contains? (free-vars %) h) (:args t)))
    :else
    (case (:op t)
      :if (and (tail-only? (:test t) h false) (tail-only? (:then t) h tail?)
               (tail-only? (:else t) h tail?))
      :let (and (tail-only? (:init t) h false) (tail-only? (:body t) h tail?))
      (not (contains? (free-vars t) h)))))

(defn- recurify [t h]
  (cond
    (and (= :app (:op t)) (self-var? (:fn t) h)) {:op :recur :args (:args t)}
    (= :if (:op t)) (assoc t :then (recurify (:then t) h) :else (recurify (:else t) h))
    (= :let (:op t)) (assoc t :body (recurify (:body t) h))
    :else t))

(defn- loop-form
  "A letrec of one fn applied at once, recursing only in tail position,
  prints as (loop [..] .. (recur ..)): the shape loop* expands to."
  [t rn]
  (let [[h] (:names t) lam (first (:inits t)) body (:body t)]
    (when (and (= 1 (count (:names t))) (not (:rest? lam))
               (= :app (:op body)) (self-var? (:fn body) h)
               (= (:arity lam) (count (:args body)))
               (not-any? #(contains? (free-vars %) h) (:args body))
               (tail-only? (:body lam) h true))
      (list 'loop (vec (mapcat (fn [p a] [(binder-name rn p (:body lam)) (->form a rn)])
                               (:names lam) (:args body)))
            (->form (recurify (:body lam) h) rn)))))

(def ^:private ^:dynamic *loop-sugar*
  "Print loop-shaped letrecs as loop/recur. Off for core->form, which
  shows the core term as it is (the REPL's :expand)."
  true)

(defn- loop-inits
  "(let [a e1] .. (let [b e2] (letrec [lam] (h a b)))) where a, b occur
  only as those arguments -> the letrec applied to e1 e2 (the shape
  loop* expands to; printing it back as (loop [x e1 ..] ..)). nil if t
  does not have that shape."
  [t]
  (loop [u t binds []]
    (if (= :let (:op u))
      (recur (:body u) (conj binds [(first (:names u)) (:init u)]))
      (when (and (seq binds) (= :letrec (:op u)) (= 1 (count (:names u)))
                 (= :app (:op (:body u)))
                 (= (map first binds) (map :name (:args (:body u))))
                 (every? #(= :var (:op %)) (:args (:body u)))
                 (let [lam (first (:inits u))
                       used (free-vars lam)]
                   (not-any? #(contains? used (first %)) binds))
                 (every? (fn [[nm init]] (not-any? #(contains? (free-vars (second %)) nm) binds))
                         binds))
        (assoc-in u [:body :args] (mapv second binds))))))

(defn- ->form [t rn]
  (let [f #(->form % rn)]
    (case (:op t)
      :var (name-of rn (:name t))
      :quote (if (:csp t)
               (symbol (str "#<csp " (:csp t) ">"))
               (literal (:datum t)))
      :resolve (:id t)
      :fn (fn-form t rn)
      :let (if-let [l (and *loop-sugar* (loop-inits t))] (f l) (let-chain t rn))
      :if (if (and (= :quote (:op (:else t))) (nil? (:datum (:else t))) (not (:csp (:else t))))
            (list 'if (f (:test t)) (f (:then t)))
            (list 'if (f (:test t)) (f (:then t)) (f (:else t))))
      :recur (apply list 'recur (map f (:args t)))
      :letrec (let [ns (:names t)
                    body (:body t)]
                (or (and *loop-sugar* (loop-form t rn))
                (if (and (= 1 (count ns)) (= :var (:op body)) (= (first ns) (:name body)))
                  (let [nm (name-of rn (first ns)) lam (first (:inits t))]
                    (list 'fn nm (params lam rn) (f (:body lam))))
                  (let [nms (mapv #(name-of rn %) ns)]
                    (list 'letfn (vec (map (fn [nm lam] (list nm (params lam rn) (f (:body lam))))
                                           nms (:inits t)))
                          (f body))))))
      :app (apply list (f (:fn t)) (map f (:args t)))
      :prim (if (= 'vector (:name t))
              (mapv f (:args t))
              (apply list (:name t) (map f (:args t))))
      :specialize (apply list 'specialize (f (:fn t)) (map f (:args t)))
      :perform (perform-form t rn)
      :handle (let [cl (cond-> (into (sorted-map) (map (fn [[k v]] [k (f v)])) (:clauses t))
                         (:return t) (assoc :return (f (:return t))))]
                (if (= :lexical (:mode t))
                  (list 'handle [(name-of rn (first (:names t))) cl] (f (:body t)))
                  (list 'handle :dynamic cl (f (:body t)))))
      :code (list 'code (f (:body t)))
      :esc (list 'esc (f (:body t)))
      :local (symbol (str "%" (:index t))))))

(defn s->form
  "Klara source of an s-term, with readable fresh names."
  [t]
  (->form t (atom {})))

(defn code->form [c] (s->form (code-term c)))

(defn core->form
  "Klara source of a core term (binder names from expansion metadata)."
  [t]
  (binding [*loop-sugar* false] (s->form (core->s t))))

(defmethod print-method Code [c ^java.io.Writer w]
  (binding [*print-meta* false]
    (.write w (pr-str (list 'code (code->form c))))))

(defmethod print-method CodeVar [v ^java.io.Writer w]
  (.write w (str "#<code-var " (:base (code-var-name v)) ">")))
