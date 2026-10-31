(ns baseline.staged-composition
  "Bounded composition probe. Re-analyze each residual; stale layout facts reject.
   This tests a proposed fact boundary, not a production fact cache or theorem."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.analysis :as analysis] [klara.compile.budget :as budget]
            [klara.compile.ir :as ir] [klara.compile.local-calls :as local]
            [klara.compile.staged :as staged] [klara.compile.unbox :as unbox]
            [klara.code :as code] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.expand :as expand]
            [klara.stage :as stage] [klara.world :as world]))

(def source
  '(fn [n]
     (let [square (fn [x] (* x x)) score (fn [x] (+ (square x) 1))]
       (loop [i 0 total 0]
         (if (< i n) (recur (inc i) (+ total (score i))) total)))))

(defn layout-facts [b term]
  (let [loops (atom [])]
    (letfn [(visit [node path]
              (budget/charge! b :work 1)
              (when (= :letrec (:op node))
                (doseq [_ (ir/nodes node)] (budget/charge! b :work 1))
                (swap! loops conj {:path path :kinds (unbox/loop-kinds node {})}))
              ;; Paths use the existing IR child order. They are local to this
              ;; source identity, not durable source coordinates across rewrites.
              (let [next-index (atom -1)]
                (ir/map-children #(do (visit % (conj path (swap! next-index inc))) %) node)))]
      (visit term [])
      {:source-id (core/code-id term) :domain :guarded-loop-layout-v1
       :entry-requires :runtime-class-guards :loops @loops})))

(defn validate-facts! [b term facts]
  (when-not (= (core/code-id term) (:source-id facts))
    (throw (ex-info "layout facts belong to another residual" {:reason :stale-analysis})))
  ;; Recomputing is intentionally conservative. A future cached checked-fact
  ;; capability may avoid this; mere identity equality is not proof of facts.
  (when-not (= facts (layout-facts b term))
    (throw (ex-info "layout facts do not follow from source" {:reason :invalid-analysis})))
  facts)

(defn observation [f argument cache]
  (try (let [value (stage/with-cache cache (ev/call-value f [argument]))]
         [:value (some-> value class .getName) value])
       (catch Throwable ex [:error (.getName (class ex)) (.getMessage ex)])))

(defn run-example []
  (let [w (world/make-world) _ (local/bootstrap! w)
        root (world/snapshot w) b (budget/budget)
        generic (expand/expand-expr source root) original (ev/run generic {:basis root})
        named (ir/named generic)
        before (layout-facts b named)
        first-pass (local/run b root named local/planner-symbol)
        middle (layout-facts b (:term first-pass))
        second-pass (local/run b root (:term first-pass) local/planner-symbol)
        after (layout-facts b (:term second-pass))
        _ (assert (= (get-in first-pass [:receipt :target-id])
                     (get-in second-pass [:receipt :source-id])) )
        stale (try (validate-facts! b (:term second-pass) middle) :unexpected
                   (catch clojure.lang.ExceptionInfo ex (ex-data ex)))
        _ (assert (= :stale-analysis (:reason stale)))
        _ (validate-facts! b (:term second-pass) after)
        residual (analysis/indexed (:term second-pass))
        residual-code (code/->code (code/core->s residual))
        prepared (staged/prevalidate (staged/prepare root residual-code {:backend :baseline :budget b}))
        function (ev/run residual {:basis root}) cache (stage/make-cache)
        _ (staged/install! cache root prepared)
        observations (mapv (fn [n]
                             (let [expected (observation original n (stage/make-cache))
                                   actual (observation function n cache)]
                               (assert (= expected actual))
                               {:argument n :observation actual}))
                           [0 1 5 5.5 11/2 5N nil :bad])]
    {:scenario :checked-local-layout-composition :source source
     :original-code-id (core/code-id generic) :residual-code-id (core/code-id residual)
     :calls-inlined (mapv :calls-inlined [first-pass second-pass])
     :receipts (mapv :receipt [first-pass second-pass])
     :facts [before middle after] :stale-fact-rejection stale
     :observations observations :usage (budget/usage b) :native-entry-stats (stage/stats cache)
     :limits [:experimental-fact-interface :fresh-analysis-per-residual
              :class-guards-still-required :no-cross-rewrite-fact-transport
              :residual-has-separate-entry-identity :no-general-composition-proof]}))

(defn run-study! [label]
  (let [report (assoc (run-example) :source-sha256
                      (into {} (for [path (concat ["verification/baseline/staged_composition.clj"]
                                                 (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                 [path (core/sha256 (slurp path))])))
        path (str "target/staged-composition/" label ".edn")]
    (io/make-parents path)
    (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:scenario :calls-inlined :stale-fact-rejection :usage :native-entry-stats])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
