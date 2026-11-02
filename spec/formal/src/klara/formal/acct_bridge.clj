(ns klara.formal.acct-bridge
  "The trusted bridge between Klara's accounts and λ-acct
  (spec/formal/src/klara/formal/acct.clj): a seeded generator of token
  programs in the fragment both express, rendered once as Klara source and
  once as a λ-acct term, and the observations compared: the outcome (a
  value, a token, an uncaught raise, an unhandled effect, or a named error)
  and the wallet and spent amount afterwards.

  Programs are generated without regard to typing, so reuse through a
  second alias, a duplicated token or a continuation resumed twice occurs
  and must be refused the same way by both (L3.affine.reuse).

  Runtime representation of λ-acct values (ansatz codegen): tagged vectors
  [ctor-index field ...]; a structure (one constructor: Store) is the vector
  of its fields; an inductive with one nullary and one other constructor
  (Live) is nil or the untagged fields; enums (Stuck) are
  nil for the first constructor and the index otherwise."
  (:require [klara.formal.acct :as m]
            [klara.host.api :as k]
            [klara.runtime.account :as acct]))

;; ---------------------------------------------------------------------------
;; λ-acct terms (de Bruijn) from the generator's named AST

(def ^:private tag
  {:var 0 :lit 1 :lam 2 :app 3 :let 4 :if 5 :tok 6 :take 7 :spend 8 :join 9 :put 10
   :raise 11 :try 12 :perform 13 :handle 14 :handling 15})

(defn- tm [k & fs] (into [(tag k)] fs))

(defn- lit-num [n] (tm :lit [2 (long n)]))

(def ^:private op-id {:op 0})

(defn ->acct
  "The λ-acct term of AST `e` under the local names `env` (innermost first)."
  [e env]
  (let [go #(->acct % env)
        idx (fn [x] (let [i (.indexOf ^java.util.List env x)] (assert (<= 0 i) x) (long i)))]
    (case (first e)
      :num (lit-num (second e))
      :nil (tm :lit [0])
      :bool (tm :lit [1 (second e)])
      :var (tm :var (idx (second e)))
      :let (let [[_ x init body] e] (tm :let (go init) (->acct body (cons x env))))
      :if (let [[_ c a b] e] (tm :if (go c) (go a) (go b)))
      :fn (let [[_ x body] e] (tm :lam (->acct body (cons x env))))
      :call (let [[_ f x] e] (tm :app (go f) (go x)))
      :take (tm :take (lit-num (second e)))
      :spend (tm :spend (go (nth e 1)) (lit-num (nth e 2)))
      :join (tm :join (go (nth e 1)) (go (nth e 2)))
      :put (tm :put (go (second e)))
      :raise (tm :raise (lit-num (second e)))
      :try (let [[_ body x handler] e] (tm :try (go body) (->acct handler (cons x env))))
      :perform (tm :perform (op-id :op) (lit-num (second e)))
      ;; clause o binds 2 = op, 1 = argument, 0 = k; r is the identity
      :handle (let [[_ [k x] clause body] e]
                (tm :handle (list (op-id :op)) (go body) (tm :var 0)
                    (->acct clause (list* k x '_op env)))))))

;; ---------------------------------------------------------------------------
;; Klara source from the same AST

(defn ->klara [e]
  (let [go ->klara]
    (case (first e)
      :num (second e)
      :nil nil
      :bool (second e)
      :var (second e)
      :let (let [[_ x init body] e] (list 'let [x (go init)] (go body)))
      :if (let [[_ c a b] e] (list 'if (go c) (go a) (go b)))
      :fn (let [[_ x body] e] (list 'fn [x] (go body)))
      :call (let [[_ f x] e] (list (go f) (go x)))
      :take (list 'a/take {:r (second e)})
      :spend (list 'a/spend (go (nth e 1)) {:r (nth e 2)})
      :join (list 'a/join (go (nth e 1)) (go (nth e 2)))
      :put (list 'a/put (go (second e)))
      :raise (list 'throw (list 'ex-info "raise" {:raised (second e)}))
      ;; only a raise is caught: named errors are stuck states of the model
      :try (let [[_ body x handler] e]
             (list 'try (go body)
                   (list 'catch 'clojure.lang.ExceptionInfo 'ex
                         (list 'if (list 'contains? '(ex-data ex) :raised)
                               (list 'let [x '(:raised (ex-data ex))] (go handler))
                               '(throw ex)))))
      :perform (list 'perform :op (second e))
      :handle (let [[_ [k x] clause body] e]
                (list 'handle {:op (list 'fn [k x] (go clause))} (go body))))))

;; ---------------------------------------------------------------------------
;; The generator

(defn- pick [^java.util.Random r xs] (nth xs (.nextInt r (count xs))))

(defn gen
  "A random program AST of depth at most `d`; `toks` and `vals` are the
  token and value locals in scope."
  [^java.util.Random r d toks vals]
  (let [tok-expr (fn [] (if (and (seq toks) (.nextBoolean r)) [:var (pick r toks)] [:take (.nextInt r 3)]))
        fresh (fn [p] (symbol (str p (.nextInt r 1000000))))]
    (if (zero? d)
      (case (.nextInt r 4)
        0 [:num (.nextInt r 3)]
        1 (if (seq vals) [:var (pick r vals)] [:nil])
        2 (tok-expr)
        [:put (tok-expr)])
      (let [sub #(gen r (dec d) toks vals)]
        (case (.nextInt r 14)
          0 (let [x (fresh "t")] [:let x (tok-expr) (gen r (dec d) (conj toks x) vals)])
          1 (let [x (fresh "v")] [:let x (sub) (gen r (dec d) toks (conj vals x))])
          2 [:spend (tok-expr) (.nextInt r 3)]
          3 [:join (tok-expr) (tok-expr)]
          4 [:put (tok-expr)]
          5 [:if [:bool (.nextBoolean r)] (sub) (sub)]
          6 (let [p (fresh "p")] [:call [:fn p (gen r (dec d) (conj toks p) vals)] (tok-expr)])
          7 [:raise (.nextInt r 3)]
          8 (let [x (fresh "e")] [:try (sub) x (gen r (dec d) toks (conj vals x))])
          9 [:let (fresh "w") [:perform (.nextInt r 3)] (sub)]
          10 (let [kk (fresh "k") x (fresh "x")]
               [:handle [kk x]
                (pick r [[:num 0]
                         [:call [:var kk] [:num 1]]
                         [:let (fresh "w") [:call [:var kk] [:num 1]] [:call [:var kk] [:num 2]]]])
                (sub)])
          ;; a token used after a computation that may consume it, or be resumed twice
          11 (let [x (fresh "t")]
               [:let x [:take (.nextInt r 2)] [:let (fresh "w") (gen r (dec d) (conj toks x) vals) [:put [:var x]]]])
          12 (let [x (fresh "t") kk (fresh "k") y (fresh "y")]
               [:handle [kk y] [:let (fresh "w") [:call [:var kk] [:num 1]] [:call [:var kk] [:num 2]]]
                [:let x [:take 1] [:let (fresh "w") [:perform 0] [:put [:var x]]]]])
          (sub))))))

;; ---------------------------------------------------------------------------
;; Running both

(def wallet 5)

(defn run-model
  "Iterate λ-acct's checked step from a store holding `wallet`; returns the
   final outcome and store."
  [term fuel]
  (loop [s [(long wallet) 0 0 nil] t term n fuel]
    (let [o (m/Acct.ev true s t)]
      (cond (zero? n) {:outcome :fuel}
            (and (vector? o) (= 1 (nth o 0))) (recur (nth o 1) (nth o 2) (dec n))
            :else {:out o :term t :store s}))))

(def ^:private stuck-name {nil :scope 1 :not-fn 2 :prim-type 3 :L3.account.insufficient 4 :L3.affine.reuse})

(defn observe-model [{:keys [out term store outcome]}]
  (if outcome
    {:outcome outcome}
    (let [[w sp] store]
      {:wallet w :spent sp
       :outcome (cond (= 0 (nth out 0)) (let [tg (nth term 0)]
                                   (case (long tg)
                                     6 :token
                                     2 :fn
                                     1 (let [d (nth term 1)] (case (long (nth d 0)) 0 nil 1 (nth d 1) 2 (nth d 1)))
                                     [:other tg]))
                      (= 2 (nth out 0)) :unhandled
                      (= 3 (nth out 0)) :uncaught
                      (= 4 (nth out 0)) (stuck-name (nth out 1) [:stuck (nth out 1)]))})))

(defn run-impl [form]
  (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
    (k/eval-string s (str "(ns accdiff (:require [klara.account :as a] [klara.effect :refer [perform handle]]))
                           (a/mint! {:r " wallet "})"))
    (let [outcome (try (let [v (k/eval-string s (pr-str form))]
                         (cond (instance? klara.runtime.value.Token v) :token
                               (fn? v) :fn
                               (instance? klara.runtime.value.Closure v) :fn
                               :else v))
                       (catch clojure.lang.ExceptionInfo e
                         (let [d (ex-data e)]
                           (cond (contains? d :raised) :uncaught
                                 (= :L3.effect.unhandled (:rule d)) :unhandled
                                 (:rule d) (:rule d)
                                 :else [:error (.getMessage e)]))))
          {:keys [balance spent]} (acct/state (:wallet @s))]
      {:wallet (:r balance 0) :spent (:r spent 0) :outcome outcome})))

(defn compare-seed [seed]
  (let [r (java.util.Random. seed)
        ast (gen r 4 [] [])
        model (observe-model (run-model (->acct ast ()) 10000))
        impl (run-impl (->klara ast))]
    {:seed seed :ast ast :form (->klara ast) :model model :impl impl :agree? (= model impl)}))
