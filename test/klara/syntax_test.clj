(ns klara.syntax-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.syntax :as s] [klara.expand :as x] [klara.core :as c]
            [klara.defs :as d] [klara.world :as w]))

(defn setup [& forms]
  (let [wo (w/make-world)] (doseq [f forms] (d/define! wo f)) wo))
(defn evaluate [wo form] (d/eval-form (w/snapshot wo) form))

(deftest syntax-values
  (let [st (s/syntax (with-meta 'x {:klara.expand/scopes #{42} :line 7 :column 3}))]
    (is (= #{42} (:scopes st)))
    (is (= {:line 7 :column 3} (:source st)))
    (is (= 'x (s/syntax->datum st)))
    (is (= :v (s/syntax-property (s/syntax-property st :k :v) :k)))
    (is (= #{42} (x/scopes (s/syntax-e (s/datum->syntax st 'y))))))
  (let [wo (setup '(defsyntax tagged [[e :body]]
                    (list 'quote-syntax (syntax-property e :tag :retained))))]
    (is (s/syntax? (evaluate wo '(quote-syntax (+ x 1)))))
    (is (= :retained (s/syntax-property (evaluate wo '(tagged x)) :tag)))
    (is (= '(+ x 1) (s/syntax->datum (evaluate wo '(quote-syntax (+ x 1))))))))

(deftest embedded-contexts
  (let [a (s/syntax (with-meta 'a {:klara.expand/scopes #{1}}))
        b (s/syntax (with-meta 'b {:klara.expand/scopes #{2}}))
        out (s/datum->syntax a (list 'new b))
        flipped (x/flip-scope b 3)]
    (is (= #{1} (x/scopes (first (s/syntax-e out)))))
    (is (= b (second (s/syntax-e out))))
    (is (= #{2 3} (:scopes flipped)))
    (is (= (:scopes flipped) (x/scopes (s/syntax-e flipped))))))

(deftest syntax-contexts-and-canonical-identity
  (let [wo (setup '(def saved (let* [x 1] (quote-syntax x)))
                  '(defsyntax escaped [] saved))]
    (is (thrown-with-msg? Exception #"unable to resolve x"
                         (evaluate wo '(let* [x 2] (escaped))))))
  (let [root w/empty-root a (x/new-ctx root) b (x/new-ctx root)
        form '(fn* [x] (quote-syntax (x x)))
        _ (dotimes [_ 7] (x/fresh-scope! b))
        ea (x/expand-recorded form root a) eb (x/expand-recorded form root b)]
    (is (= (:code-id ea) (:code-id eb)))
    (is (= (c/canonical (:term ea)) (c/canonical (:term eb))))))

(deftest composite-context-and-syntax-literal-memo
  (let [wo (setup '(defsyntax quote-input [[e :body]] (list 'quote-syntax e)))
        context (evaluate wo '(let* [x 1] (quote-syntax (x x))))]
    (is (seq (:scopes context)))
    (is (= (:scopes context) (x/scopes (s/syntax-e (s/datum->syntax context 'y)))))
    (let [table (atom {}) form '(fn* [x] (quote-input x))
          expand #(binding [x/*memo* {:key x/alpha-key :table table}]
                    (x/expand-recorded form (w/snapshot wo)))
          a (expand) b (expand)]
      (is (empty? @table))
      (is (= (:code-id a) (:code-id b)))
      (is (= (c/canonical (:term a)) (c/canonical (:term b)))))))

(deftest nested-hygiene-and-local-expansion
  (let [wo (setup
             '(defsyntax inner [[e :expr]] (list 'let* ['tmp 100] e))
             '(defsyntax outer [[e :expr]] (list 'inner e))
             '(defsyntax checked [[e :expr]] (local-expand e)))]
    (is (= 7 (evaluate wo '(let* [tmp 7] (outer tmp)))))
    (is (= 9 (evaluate wo '(let* [x 9] (checked x)))))
    (is (= 9 (evaluate wo '(let* [x 9] (checked (let* [x 1] (+ x 8)))))))
    (d/define! wo '(defsyntax under [[e :expr]] (list 'let* ['x 100] (local-expand e))))
    (is (= 9 (evaluate wo '(let* [x 9] (under x)))))
    (is (= [2 3] (evaluate wo '(let* [x 2] [(checked x) (let* [x 3] (checked x))]))))))

(deftest grammar-and-failures
  (let [wo (setup
             '(defsyntax scoped [[b :binding] [e :expr] [body :body ...]]
                (list* 'let* [b e] body))
             '(defsyntax maybe [:then [e :expr] (:optional [other :expr])]
                (list 'vector e other)))]
    (is (= 5 (evaluate wo '(scoped x 3 (+ x 2)))))
    (is (= [4 nil] (evaluate wo '(maybe :then 4))))
    (is (= [4 5] (evaluate wo '(maybe :then 4 5))))
    (doseq [[form expected] [['(scoped 17 3) "binding identifier"]
                           ['(maybe :else 4) ":then"]
                           ['(maybe :then) "argument matching"]
                           ['(maybe :then 1 2 3) "end of form"]]]
      (let [err (try (evaluate wo form) (catch Exception e e))]
        (is (instance? Exception err))
        (is (re-find (re-pattern expected) (ex-message err)))))
    (let [bad (with-meta '(+ 1 2) {:file "grammar.k" :line 12 :column 5})
          err (try (evaluate wo (list 'scoped bad 3)) (catch Exception e e))]
      (is (= {:file "grammar.k" :line 12 :column 5} (:source (ex-data err))))
      (is (re-find #"grammar.k:12:5" (ex-message err))))))

(deftest missing-arguments-and-malformed-classes-have-locations
  (let [wo (setup '(defsyntax required [[e :expr]] e)
                  '(defsyntax-class pair [[a :body] [b :body]])
                  '(defsyntax consume [[p :pair]] 1))]
    (doseq [[form expected path] [['(required) "argument matching" [0]]
                                ['(consume 17) "syntax sequence" [0]]
                                ['(consume [1]) "argument matching" [0 1]]]]
      (let [form (with-meta form {:file "missing.k" :line 8 :column 2})
            err (try (evaluate wo form) (catch Exception e e))]
        (is (re-find (re-pattern expected) (ex-message err)))
        (is (= path (:path (ex-data err))))
        (is (re-find #"missing.k:8:2" (ex-message err)))))))

(deftest memo-work-and-read-replay
  (let [wo (setup '(defsyntax checked [[e :body]] (local-expand e)))
        root (w/snapshot wo) table (atom {})
        a (x/new-ctx root) b (x/new-ctx root)
        form '(fn* [x] [(checked (inc x)) (checked (inc x))])
        expand #(binding [x/*memo* {:key x/alpha-key :table table}]
                  (x/expand-recorded form root %))
        first-result (expand a) second-result (expand b)]
    (is (= 1 (count @table)))
    (is (= 1 (count (filter #(= :macro (:event %)) @(:log a)))))
    (is (= 0 (count (filter #(= :macro (:event %)) @(:log b)))))
    (is (= (:term first-result) (:term second-result)))
    (is (= (:reads first-result) (:reads second-result)))
    (is (contains? (:reads second-result) [:absent 'inc]))))

(deftest definition-contexts
  (let [wo (setup
             '(defsyntax locally [[e :body]]
                (let [dc (definition-context)]
                  (bind-syntax! dc (quote-syntax private) (fn [v] (list '+ v 10)))
                  (local-expand e dc))))]
    (is (= 15 (evaluate wo '(locally (private 5)))))
    (is (thrown-with-msg? Exception #"unable to resolve private"
                         (evaluate wo '(private 5))))
    (is (thrown-with-msg? Exception #"no expansion context"
                         (x/local-expand (s/syntax 1))))))

(deftest reusable-classes-and-pattern-composition
  (let [wo (setup
             '(defsyntax-class pair [[a :expr] [b :expr]])
             '(defsyntax add-pair [[p :pair]]
                (list '+ (syntax-attribute p 'a) (syntax-attribute p 'b)))
             '(defsyntax clauses [(:repeat (:item [v :expr])) :end
                                 (:optional (:otherwise [fallback :expr]))]
                (if fallback fallback (list* 'vector v))))]
    (is (= 7 (evaluate wo '(let* [x 3] (add-pair [x 4])))))
    (is (= [1 2] (evaluate wo '(clauses (:item 1) (:item 2) :end))))
    (is (= [] (evaluate wo '(clauses :end))))
    (is (= 9 (evaluate wo '(clauses (:item 1) :end (:otherwise 9)))))
    (is (thrown-with-msg? Exception #"end of form"
                         (evaluate wo '(add-pair [1 2 3]))))
    (let [r (x/expand-recorded '(add-pair [1 2]) (w/snapshot wo))]
      (is (some #(= [:value 'pair] (subvec % 0 2)) (:reads r))))
    (d/define! wo '(def uses-pair (fn* [] (add-pair [3 4]))))
    (let [table (atom {}) form '(fn* [x] (add-pair [x 4]))
          cached #(binding [x/*memo* {:key x/alpha-key :table table}]
                    (x/expand-recorded form (w/snapshot wo)))
          before (cached)]
      (d/define! wo '(defsyntax-class pair [[b :expr] [a :expr]]))
      (is (= ['uses-pair] (:reexpanded (d/invalidate! wo 'pair))))
      (let [after (cached) fresh (x/expand-recorded form (w/snapshot wo))]
        (is (not= (:term before) (:term after)))
        (is (= (:term fresh) (:term after)))
        (is (= (:reads fresh) (:reads after)))))
    (is (thrown-with-msg? Exception #"distinct pattern variables"
                         (d/define! wo '(defsyntax bad [[e :expr] [e :expr]] e))))))

(deftest nested-definition-context-hygiene-and-lifetime
  (let [wo (setup
             '(def saved-context (atom nil))
             '(defsyntax outer-context [[e :body]]
                (let [dc (definition-context)]
                  (reset! saved-context dc)
                  (bind-syntax! dc (quote-syntax private) (fn [] 1))
                  (bind-syntax! dc (quote-syntax via) (fn [] (list 'private)))
                  (local-expand e dc)))
             '(defsyntax inner-context [[e :body]]
                (let [dc (definition-context)]
                  (bind-syntax! dc (quote-syntax private) (fn [] 2))
                  (local-expand e dc)))
             '(defsyntax escaped-context [[e :body]] (local-expand e @saved-context)))]
    (is (= [1 2] (evaluate wo '(outer-context (inner-context [(via) (private)])))))
    (is (thrown-with-msg? Exception #"definition context escaped"
                         (evaluate wo '(escaped-context 1))))))

(deftest expressions-expand-once-and-report-source
  (let [wo (setup
             '(def calls (atom 0))
             '(defsyntax counted [] (do (swap! calls inc) 7))
             '(defsyntax identity-syntax [[e :expr]] e))]
    (is (= 7 (evaluate wo '(identity-syntax (counted)))))
    (is (= 1 @(d/lookup (w/snapshot wo) 'calls)))
    (let [bad (with-meta '(identity-syntax no-such-expression)
                        {:file "expr.k" :line 4 :column 2})
          err (try (evaluate wo bad) (catch Exception e e))]
      (is (= "expression" (:expected (ex-data err))))
      (is (= 4 (get-in (ex-data err) [:source :line]))))))

(deftest cache-reads-and-forks
  (let [wo (setup
             '(def schema 2)
             '(defsyntax checked [[e :body]] (local-expand (list '+ e schema))))
        table (atom {})
        cached (fn [form] (binding [x/*memo* {:key x/alpha-key :table table}]
                           (x/expand-recorded form (w/snapshot wo))))
        form '(fn* [x] [(checked (inc x)) (checked (inc x))])
        first-result (cached form)
        second-result (cached form)]
    (is (= (:term first-result) (:term second-result)))
    (is (= (:reads first-result) (:reads second-result)))
    (is (contains? (:reads second-result) [:absent 'inc]))
    (is (some #(= [:value 'schema] (subvec % 0 2)) (:reads second-result)))
    (d/define! wo '(defsyntax inc [[e :expr]] (list '+ e 100)))
    (d/define! wo '(def schema 3))
    (let [cached-result (cached form) fresh (x/expand-recorded form (w/snapshot wo))]
      (is (= (:term fresh) (:term cached-result)))
      (is (= (:reads fresh) (:reads cached-result)))
      (is (not= (:term first-result) (:term cached-result))))
    ;; Changing the transformer itself must also evict its memo entry.
    (d/define! wo '(defsyntax checked [[e :body]] (local-expand (list '+ e schema 1))))
    (let [cached-result (cached form) fresh (x/expand-recorded form (w/snapshot wo))]
      (is (= (:term fresh) (:term cached-result)))
      (is (= (:reads fresh) (:reads cached-result))))
    (d/define! wo '(def use-checked (fn* [x] (checked (inc x)))))
    (let [fork (w/fork wo)]
      (d/define! fork '(defsyntax inc [[e :expr]] (list '+ e 1000)))
      (d/invalidate! fork 'inc)
      (is (= 105 (evaluate wo '(use-checked 1))))
      (is (= 1005 (evaluate fork '(use-checked 1)))))))
