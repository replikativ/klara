(ns consolidation.world-evolution
  "Reproduce guest optimizer-policy evolution through existing world operations.
   This demonstrates in-memory branch/merge/pinning, not durable snapshots,
   a self-hosted native compiler, or a semantic proof gate on definition merge."
  (:require [klara.authority :as authority] [klara.defs :as defs]
            [klara.eval :as ev] [klara.world :as world]))

(defn run-experiment! []
  (let [w (world/make-world) fiber (world/fiber w) store (authority/new-store)
        evaluate (fn [form]
                   (world/raise-basis! fiber)
                   (binding [authority/*store* store ev/*fiber* fiber]
                     (if (and (seq? form) (#{'def 'defn 'defmacro} (first form)))
                       (defs/define! w form)
                       (defs/eval-in fiber form))))]
    (evaluate '(def compiler-world (perform :world/fork)))
    (evaluate '(perform :world/eval-in compiler-world '(def choose-pass (fn [profile] :generic))))
    (evaluate '(def old-policy (perform :world/eval-in compiler-world '(fn [profile] (choose-pass profile)))))
    (evaluate '(def compiler-branch (branch! {:compiler compiler-world})))
    (evaluate '(perform :world/eval-in (system compiler-branch :compiler)
                        '(def choose-pass (fn [profile] (if (>= (:calls profile) 100) :prefix-fold :generic)))))
    (let [before (evaluate '[(perform :world/eval-in compiler-world '(choose-pass {:calls 1000}))
                            (perform :world/eval-in (system compiler-branch :compiler) '(choose-pass {:calls 1000}))
                            (old-policy {:calls 1000})])
          merged (evaluate '(merge! compiler-branch))
          after (evaluate '[(perform :world/eval-in compiler-world '(choose-pass {:calls 1000}))
                           (old-policy {:calls 1000})])
          compiler-world (defs/lookup (world/snapshot w) 'compiler-world)
          definition (world/entry* (world/snapshot compiler-world) 'choose-pass)]
      ;; A runtime-value definition is a separate API and has no retained source.
      (evaluate '(perform :world/eval-in compiler-world '(perform :world/define 'runtime-state [1 2])))
      (let [value-entry (world/entry* (world/snapshot compiler-world) 'runtime-state)
            replayed (world/make-world)
            _ (defs/define! replayed (:form definition))
            replay-root (world/snapshot replayed)
            replay-output (defs/eval-form replay-root '(choose-pass {:calls 1000}))
            same-code-id (= (:code-id definition) (:code-id (world/entry* replay-root 'choose-pass)))
            trace {:before-merge before :merge merged :after-merge after
                   :definition {:source-form (:form definition) :has-Core (contains? definition :code)
                                :code-id (:code-id definition) :reads (:reads definition)}
                   :source-replay {:output replay-output :same-code-id same-code-id
                                   :scope :one-closed-definition-same-host}
                   :value-only-definition {:has-source (contains? value-entry :form)
                                           :has-Core (contains? value-entry :code)}
                   :evidence :tested-in-memory-guest-policy-evolution
                   :not-established [:proved-policy-change :proof-gated-definition-merge
                                     :host-compiler-evolution :durable-image :resumable-checkpoint]}]
        (when-not (and (= [:generic :prefix-fold :generic] before)
                       (= {:merged [:compiler]} merged)
                       (= [:prefix-fold :generic] after)
                       (:form definition) (:code definition)
                       (= :prefix-fold replay-output) same-code-id
                       (not (contains? value-entry :form)))
          (throw (ex-info "guest policy evolution experiment failed" trace)))
        trace))))
