(ns klara.entry-test
  (:require [clojure.test :refer [deftest is]] [klara.stage :as stage]
            [klara.world :as world] [klara.defs :as defs]
            [klara.compile.core :as compiler]))

(def live-root :expected)
(def ^:dynamic *dynamic-root* :expected)

(defn fixture []
  (let [w (world/make-world)] (defs/define! w '(def f (fn [x] (+ x 1))))
    {:world w :root (world/snapshot w) :f (defs/lookup (world/snapshot w) 'f)}))

(defn with-guards [exe guards]
  (let [cert (assoc (:certificate exe) :assumptions (set guards))]
    (assoc exe :guards guards :certificate (assoc cert :digest (stage/digest cert)))))

(defn handwritten [f guards variant priority]
  (assoc (stage/executable f guards inc {:test :entry}) :guards (vec guards)
         :selection {:variant variant :priority priority}))

(deftest planned-and-reference-entry-observe-live-and-dynamic-roots
  (let [{:keys [root f]} (fixture) cache (stage/make-cache)
        ordinary (handwritten f [[:host-root 'klara.entry-test/live-root :expected]] :live 0)]
    (stage/install! cache ordinary)
    (doseq [mode [:reference :planned]]
      (binding [stage/*entry-mode* mode]
        (is (some? (stage/enter cache f [] [1] root [])))
        (with-redefs [live-root :changed] (is (nil? (stage/enter cache f [] [1] root []))))
        (is (some? (stage/enter cache f [] [1] root [])))))
    (stage/clear! cache)
    (stage/install! cache (handwritten f [[:host-root 'klara.entry-test/*dynamic-root* :expected]] :dynamic 0))
    (is (some? (stage/enter cache f [] [1] root [])))
    (binding [*dynamic-root* :changed] (is (nil? (stage/enter cache f [] [1] root [])))))
  (let [{:keys [root f]} (fixture) cache (stage/make-cache)
        prefix (symbol (str "klara.entry-target-" (gensym))) other (symbol (str prefix "-alias"))
        n (create-ns prefix) alternate (create-ns other) marker (Object.)
        sym (symbol (str prefix) "probe")]
    (try
      (intern n 'probe marker) (intern alternate 'probe :changed)
      (stage/install! cache (handwritten f [[:host-root sym marker]] :namespace 0))
      (ns-unmap n 'probe) (intern n 'probe marker)
      (is (some? (stage/enter cache f [] [1] root [])) "replacement Var with the same value is valid")
      (binding [*ns* (the-ns 'klara.entry-test)]
        (.addAlias ^clojure.lang.Namespace *ns* prefix alternate)
        (try (is (nil? (stage/enter cache f [] [1] root [])) "respect the caller's namespace alias")
             (finally (.removeAlias ^clojure.lang.Namespace *ns* prefix))))
      (alter-var-root (ns-resolve n 'probe) (constantly :changed))
      (is (nil? (stage/enter cache f [] [1] root [])))
      (finally (remove-ns prefix) (remove-ns other)))))

(deftest opaque-argument-predicates-remain-ordered-and-host-roots-are-not-memoized
  (let [{:keys [root f]} (fixture) cache (stage/make-cache) calls (atom [])
        guards [[:host-root 'klara.entry-test/live-root :expected] [:arg 0 ::mutate]]]
    (stage/install! cache (handwritten f guards :first 10))
    (stage/install! cache (handwritten f [[:host-root 'klara.entry-test/live-root :expected]] :second 0))
    (doseq [mode [:reference :planned]]
      (reset! calls [])
      (with-redefs [live-root :expected
                    stage/preds (assoc stage/preds ::mutate
                                       (fn [_] (swap! calls conj :argument)
                                         (alter-var-root #'live-root (constantly :changed)) false))]
        (binding [stage/*entry-mode* mode]
          (is (nil? (stage/enter cache f [] [1] root [])))
          (is (= [:argument] @calls)))))))

(deftest unresolved-host-bindings-are-not-resolved-at-installation
  (let [{:keys [root f]} (fixture) cache (stage/make-cache) calls (atom [])
        sym 'klara.not-loaded.entry/probe marker (Object.) resolve clojure.core/requiring-resolve]
    (with-redefs [clojure.core/requiring-resolve
                  (fn [s] (if (= sym s) (do (swap! calls conj s) (atom marker)) (resolve s)))]
      (stage/install! cache (handwritten f [[:arg 0 :double] [:host-root sym marker]] :first 0))
      (is (empty? @calls))
      (is (nil? (stage/enter cache f [] [1] root [])))
      (is (empty? @calls))
      (is (some? (stage/enter cache f [] [1.5] root [])))
      (is (= [sym] @calls)))))

(deftest cleared-binding-generation-is-a-conservative-cache-miss
  (let [{:keys [root f]} (fixture) cache (stage/make-cache)]
    (stage/install! cache (handwritten f [[:host-root 'klara.entry-test/live-root :expected]] :live 0))
    (let [installed (first (stage/executables cache))
          generation (get-in installed [::stage/runtime-plan 0 1 2])]
      (.clear ^java.lang.ref.WeakReference generation)
      (is (some? (stage/enter cache f [] [1] root [])))
      (with-redefs [live-root :changed] (is (nil? (stage/enter cache f [] [1] root [])))))))

(deftest direct-site-reconsiders-preferred-and-previously-failing-host-guards
  (let [{:keys [world root f]} (fixture)
        exe (compiler/compile-def world 'f {:mode :baseline}) cache (stage/make-cache)
        high (assoc (with-guards exe (conj (vec (:guards exe)) [:host-root 'klara.entry-test/live-root :expected]))
                    :selection {:variant :high :priority 10})
        low (assoc exe :selection {:variant :low :priority 0}) site (:direct-entry @cache)]
    (stage/install! cache high) (stage/install! cache low)
    (with-redefs [live-root :changed]
      (is (= :low (get-in (site f [1] root) [:selection :variant])))
      (alter-var-root #'live-root (constantly :expected))
      (is (= :high (get-in (site f [1] root) [:selection :variant])))
      (alter-var-root #'live-root (constantly :changed))
      (is (= :low (get-in (site f [1] root) [:selection :variant]))))
    (stage/clear! cache) (stage/install! cache high)
    (with-redefs [live-root :changed]
      (is (nil? (site f [1] root)))
      (alter-var-root #'live-root (constantly :expected))
      (is (= :high (get-in (site f [1] root) [:selection :variant]))))))

(deftest direct-site-keeps-live-guard-failure-order-and-rejects-handler-contexts
  (let [{:keys [world root f]} (fixture) cache (stage/make-cache)
        exe (compiler/compile-def world 'f {:mode :baseline})
        guarded (with-guards exe (into [[:host-root 'klara.not-loaded.entry/probe :expected]]
                                       (conj (vec (:guards exe)) [:arity 2])))
        site (:direct-entry @cache) resolve clojure.core/requiring-resolve]
    (stage/install! cache guarded)
    (with-redefs [clojure.core/requiring-resolve
                  (fn [s] (if (= s 'klara.not-loaded.entry/probe)
                            (throw (ex-info "live guard reached" {:test :ordered})) (resolve s)))]
      (is (thrown? clojure.lang.ExceptionInfo (site f [1] root))))
    (stage/clear! cache) (stage/install! cache exe)
    (is (nil? (site f 1 root [[{:tag :handle :mode :dynamic :clauses {:exn/raise :handler}}]])))
    (is (some? (site f 1 root [])))))

(deftest guard-evaluator-overrides-are-not-bypassed
  (let [{:keys [root f]} (fixture) cache (stage/make-cache)
        exe (handwritten f [[:host-root 'klara.entry-test/live-root :expected]] :live 0)]
    (with-redefs [stage/guard-holds? (constantly false)]
      (stage/install! cache exe)
      (is (nil? (stage/enter cache f [] [1] root []))))
    (is (some? (stage/enter cache f [] [1] root [])))
    (stage/clear! cache) (stage/install! cache exe)
    (with-redefs [stage/guard-holds? (constantly false)]
      (is (nil? (stage/enter cache f [] [1] root []))))))

(deftest colliding-code-id-entries-coexist-and-respect-implementation-identity
  (let [term-id (ns-resolve 'klara.stage 'term-code-id)
        slot #(bit-and (System/identityHashCode %) 511)
        [a b] (first (filter #(> (count %) 1)
                            (vals (group-by slot (repeatedly 513 #(hash-map :op :quote :datum (Object.)))))))
        calls (atom [])]
    (with-redefs [klara.core/code-id (fn [t] (swap! calls conj t) (if (identical? a t) "a" "b"))]
      (dotimes [_ 8] (is (= ["a" "b"] [(term-id a) (term-id b)])))
      (is (= 2 (count @calls))))
    (with-redefs [klara.core/code-id (constantly "changed-implementation")]
      (is (= "changed-implementation" (term-id a))))))
