(ns klara.compile.relation
  "Common admission for baseline recipe chains. Binds named source syntax to
   the original indexed entry and checks opaque edges through the residual.
   This is structural evidence admission, not a semantic equivalence proof."
  (:require [klara.compile.analysis :as analysis] [klara.compile.edge :as edge]
            [klara.compile.diagnostics :as diagnostics]
            [klara.compile.subject :as subject] [klara.compile.inline-check :as syntax] [klara.core :as core]))

(defn check [exe]
  (diagnostics/phase :source-relation {}
  (try
    (let [edges (:checked-edges exe) origin (:rewrite-origin exe)
          named-source (or origin (:ir exe))
          indexed-source (analysis/indexed named-source)]
      (core/assert-wf! indexed-source)
      (cond
        (not= (:code-id exe) (core/code-id indexed-source)) :relation-source
        (and (nil? origin) (or (seq edges) (seq (:rewrite-receipts exe)) (:rewrite-origin-id exe))) :relation-origin
        (and origin (not= (:rewrite-origin-id exe) (core/code-id origin))) :relation-origin
        (and origin (not (edge/chain-valid? edges (core/code-id origin)
                                            (core/code-id (:ir exe)) subject/core-contract))) :relation-chain
        (some (fn [e]
                (when (= :local-call-inline-v1 (:rule (edge/info e)))
                  (let [info (edge/info e)
                        checked (syntax/check! nil (edge/source e) (edge/target e) (mapv :at (:bindings info)))]
                    (not= checked (:syntax-correspondence info))))) edges) :relation-local-syntax
        (not= (or (:rewrite-receipts exe) []) (mapv edge/info edges)) :relation-receipts
        :else nil))
    (catch Exception _ :relation-malformed))))

(defn summary [exe]
  {:source-id (:code-id exe) :target-id (core/code-id (:ir exe))
   :contract subject/core-contract :source-binding :checked-index-reconstruction
   :rules (mapv :rule (:rewrite-receipts exe))
   :evidence :hosted-checked-recipes :whole-chain-kernel-proof? false})
