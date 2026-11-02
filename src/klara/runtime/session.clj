(ns klara.runtime.session
  "Sessions (spec/L1-worlds.md#sessions-and-activations): the only mutable
  cell in the model, its default effect handlers, and source loading.

  A session holds its current world, a bounded history of summaries
  (L1.retain.history), its current namespace and source roots."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [klara.lang.builtins :as b]
            [klara.lang.expand :as ex]
            [klara.lang.term :as t]
            [klara.runtime.account :as account]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Code World]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Session state

(defn new-session
  ([] (new-session {}))
  ([{:keys [roots out history-limit]
     :or {roots ["src" "lib" "examples"] history-limit 1000}}]
   (atom {:world (w/empty-world)
          :history clojure.lang.PersistentQueue/EMPTY
          :history-limit history-limit
          :ns 'user
          :roots roots
          :wallet (account/root-wallet)                          ; L3.account.wallet
          :out (or out *out*)})))

(defn current-world [session] (:world @session))

(defn publish!
  "Publish the changes of world `changed` to the session (L1.session.publish).
   Returns the published world."
  [session ^World changed]
  (let [result (volatile! nil)]
    (swap! session
           (fn [s]
             (let [merged (w/apply-delta changed (:world s))]
               (when-not merged
                 (fail :L1.session.conflict
                       (str "concurrent change to the same definitions while publishing " (w/id changed))))
               (vreset! result merged)
               (let [h (conj (:history s) {:id (w/id merged) :parent (w/id (:world s))
                                           :changed (w/changed-names (:world s) merged)})
                     h (if (> (count h) (:history-limit s)) (pop h) h)]
                 (assoc s :world merged :history h)))))
    @result))

;; ---------------------------------------------------------------------------
;; Default handlers (L3.effect.default)

(defn- out-write [session s]
  (let [^java.io.Writer out (:out @session)]
    (.write out ^String s) (.flush out)))

(defn compiling-ms
  "Milliseconds the host's JIT compiler has spent so far, or nil where the
   host does not say (L3.effect.time)."
  []
  (let [b (java.lang.management.ManagementFactory/getCompilationMXBean)]
    (when (and b (.isCompilationTimeMonitoringSupported b)) (.getTotalCompilationTime b))))

(defn session-defaults [session]
  {:io/print (fn [st [s]] (out-write session s) (assoc st :mode :ret :ctl nil :env nil))
   ;; L3.effect.time: the host's monotonic clock, in nanoseconds
   :time/now (fn [st _] (assoc st :mode :ret :ctl (System/nanoTime) :env nil))
   :time/compiling (fn [st _] (assoc st :mode :ret :ctl (compiling-ms) :env nil))
   :world/define (fn [st [q info]]
                   (let [base (:world st)
                         changed (w/put-definition base q (w/definition q info))
                         published (publish! session changed)]
                     ;; L1.def.read-your-writes
                     (assoc st :mode :ret :ctl q :env nil :world published)))
   :world/update (fn [st [f]]
                   (let [base (:world st)
                         published (publish! session (f base))]
                     (assoc st :mode :ret :ctl nil :env nil :world published)))})

(defn session-dyn [session]
  {:meter nil :wallet (:wallet @session) :defaults (session-defaults session) :session session :job nil})

(defn activation
  "Evaluate a Core term as a top-level activation (L1.context.top)."
  [session term]
  (m/eval-term term (current-world session) (session-dyn session)))

;; ---------------------------------------------------------------------------
;; Expansion against the session

(defn- macro-runner [session]
  (fn [d form]
    (m/call-in [(current-world session) nil (session-dyn session)]
               (:value d) (vec (rest form)))))

(defn resolver [session ns-sym]
  (let [world (current-world session)]
    {:ns ns-sym
     :defined (fn [q] (w/lookup world q))
     :ns-info (fn [n] (w/ns-info world n))
     :run-macro (macro-runner session)}))

(defn expand [session form]
  (ex/expand (ex/env (resolver session (:ns @session))) form))

(defn eval-form [session form]
  (activation session (expand session form)))

;; ---------------------------------------------------------------------------
;; Loading (L1.module.*)

(defn- ns->paths [ns-sym]
  (let [base (-> (str ns-sym) (str/replace "-" "_") (str/replace "." "/"))]
    [(str base ".clj") (str base ".cljc")]))

(defn find-source
  "The file or classpath resource defining `ns-sym` on the session roots."
  [session ns-sym]
  (or (some (fn [root] (some (fn [p] (let [f (io/file root p)] (when (.exists f) f)))
                             (ns->paths ns-sym)))
            (:roots @session))
      (some #(io/resource %) (ns->paths ns-sym))))

(defn eval-reader
  "Evaluate every form from `reader` in order, each as an activation
   (L1.module.load). Returns the last value."
  [session ^java.io.Reader reader]
  (let [r (clojure.lang.LineNumberingPushbackReader. reader)]
    (loop [last nil]
      (let [form (ex/read-all r (:ns @session))]
        (if (ex/eof? form)
          last
          (let [before (current-world session)
                v (eval-form session form)]
            ;; hooks of the host (klara.host.precompile), with the world before
            (doseq [h (:after-form @session)] (h session before))
            (recur v)))))))

(defn eval-string [session s]
  (eval-reader session (java.io.StringReader. s)))

(defn load-source!
  "Load file `src`; the namespaces it creates are recorded as coming from it
   (:ns-sources), so the host can tell a program's code from libraries."
  [session src]
  (let [saved (:ns @session)
        known (set (keys (w/namespaces (current-world session))))]
    (try (binding [ex/*source-file* (str src)]
           (with-open [r (io/reader src)] (eval-reader session r)))
         (finally
           (swap! session assoc :ns saved)
           ;; a library required while this file loads was recorded by its own
           ;; load first; that record stays
           (swap! session update :ns-sources
                  (fn [m] (merge (into {} (for [n (keys (w/namespaces (current-world session)))
                                                :when (not (contains? known n))]
                                            [n (if (instance? java.io.File src)
                                                 (.getAbsolutePath ^java.io.File src)
                                                 (str src))]))
                                 m)))))))

(defn loaded?
  "Runtime namespaces need no file, but a library file of the same name may
   extend one (klara.jit is runtime functions plus Klara code)."
  [session ns-sym]
  (or (some? (w/ns-info (current-world session) ns-sym))
      (and (b/runtime-ns? ns-sym) (nil? (find-source session ns-sym)))))

(defn- ensure-ns [world ns-sym]
  (if (w/ns-info world ns-sym)
    world
    (w/update-namespace world ns-sym (fn [_] {:aliases {} :refers {} :exclude #{}}))))

(defn require-lib!
  "Load `lib` if needed and record aliases/refers in `ns-sym` (L1.module.require)."
  [session ns-sym spec]
  (let [[lib & opts] (if (sequential? spec) spec [spec])
        opts (apply hash-map opts)]
    (when-not (loaded? session lib)
      (if-let [src (find-source session lib)]
        (load-source! session src)
        (fail :L1.module.require (str "cannot find namespace " lib " on " (:roots @session)) :ns lib)))
    (let [world (current-world session)
          names (fn [] (->> (keys (w/defs world)) (filter #(= (str lib) (namespace %))) (map (comp symbol name))))
          refers (let [r (:refer opts)]
                   (cond (= :all r) (if (b/runtime-ns? lib)
                                      (->> (keys @b/registry) (filter #(= (str lib) (namespace %))) (map (comp symbol name)))
                                      (names))
                         :else r))
          alias (:as opts)]
      (when alias (ex/mirror-alias! ns-sym alias lib))
      (doseq [s refers] (ex/mirror-refer! ns-sym s (symbol (str lib) (name s))))
      (publish! session
                (w/update-namespace (ensure-ns world ns-sym) ns-sym
                                    (fn [info]
                                      (cond-> info
                                        alias (assoc-in [:aliases alias] lib)
                                        (seq refers) (update :refers merge
                                                             (into {} (map (fn [s] [s (symbol (str lib) (name s))])) refers)))))))))

(defn- unquote* [x] (if (and (seq? x) (= 'quote (first x))) (second x) x))

(defn ns-directive!
  "(ns name (:require ...) (:refer-clojure :exclude [...])) (L1.module.ns)."
  [session form]
  (let [[_ name & clauses] form
        clauses (filter seq? clauses)
        world (current-world session)]
    (swap! session assoc :ns name)
    (publish! session (ensure-ns world name))
    (doseq [[kind & args] clauses]
      (case kind
        :require (doseq [spec args] (require-lib! session name spec))
        :refer-clojure (let [{:keys [exclude]} (apply hash-map args)
                             world (current-world session)]
                         (publish! session
                                   (w/update-namespace world name #(update % :exclude into exclude))))
        nil))
    nil))

;; ---------------------------------------------------------------------------
;; Directive intrinsics: they run outside the machine's own effects because
;; loading is a sequence of activations; afterwards the activation continues
;; in the session's current world.

(defn- directive [f]
  {:kind :intrinsic
   :fn (fn [st [form _ns]]
         (let [session (get-in st [:dyn :session])]
           (when-not session (fail :L1.module.require "namespace directives need a session"))
           (when (get-in st [:dyn :job]) (fail :L1.module.require "namespace directives are not available inside a job"))
           (f session form)
           (assoc st :mode :ret :ctl nil :env nil :world (current-world session))))})

(b/register! 'klara.kernel/ns (directive ns-directive!))
(b/register! 'klara.kernel/in-ns
             (directive (fn [session [_ q]]
                          (let [n (unquote* q) world (current-world session)]
                            (swap! session assoc :ns n)
                            (publish! session (ensure-ns world n))))))
(b/register! 'klara.kernel/require
             (directive (fn [session [_ & specs]]
                          (doseq [s specs] (require-lib! session (:ns @session) (unquote* s))))))

;; ---------------------------------------------------------------------------
;; Retention report (design/01-lifetimes.md#making-retention-visible)

(defn retained [session]
  (let [s @session]
    {:world (w/id (:world s))
     :world-definitions (count (w/defs (:world s)))
     :history-entries (count (:history s))
     :history-limit (:history-limit s)
     :candidates (reduce + 0 (map (comp count :compiled) (vals (w/defs (:world s)))))
     :candidates-by-name (into {} (keep (fn [[q d]] (when (seq (:compiled d)) [q (count (:compiled d))])))
                               (w/defs (:world s)))}))

(b/register! 'klara.kernel/retained
             {:kind :intrinsic
              :fn (fn [st _]
                    (assoc st :mode :ret :env nil
                           :ctl (assoc (retained (get-in st [:dyn :session]))
                                       :jobs (count (filter #(= :job (:f %)) (:k st))))))})
