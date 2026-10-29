(ns klara.repl
  "An interactive Klara REPL over T0: read (Clojure syntax), expand,
  evaluate, print. `clojure -M:repl` starts it; the prompt is `k=>`.

  A SESSION holds named worlds (forks) and the name of the current one.
  Every top-level form is expanded and evaluated against the current
  world's root. A (def ..) or (defmacro ..) is published with
  klara.defs/define! and its dependents are invalidated at once (the
  REPL is a convenience layer: it repairs instead of leaving dependents
  pending; the report is printed as `;; stale: ..` / `;; cutoff: ..`).

  Commands are keywords in the repl namespace (as clojure.main's :repl/quit);
  any other keyword evaluates to itself:
    :repl/world            definitions of the current world, with versions
    :repl/basis            current world name and root version
    :repl/fork <name>      fork the current world as <name> and switch to it
    :repl/switch <name>    switch to world <name>
    :repl/expand <form>    show the core term of <form>, printed as source
    :repl/code <form>      evaluate <form> to a code value, pretty-print it
    :repl/help             this list

  Errors print as `!! <kind>: <message>` and never end the session.

  `eval-string` runs a string of forms in a session and returns the
  printed output (lines joined by newlines); the transcript harness
  (test/klara/transcript_test.clj) is built on it."
  (:require [clojure.pprint :as pp]
            [clojure.string :as str]
            [klara.authority :as a]
            [klara.code :as code]
            [klara.world :as w]
            [klara.expand :as x]
            [klara.eval :as ev]
            [klara.defs :as d]
            [klara.stage :as stage]
            [klara.compile.core :as compiler])
  (:import [clojure.lang LineNumberingPushbackReader]
           [java.io StringReader]))

(defn session
  "A fresh REPL session: one empty world named main, and its own
  authority store (klara.authority)."
  []
  {:worlds (atom {"main" {:world (w/make-world) :parent nil}})
   :current (atom "main")
   :cache (stage/make-cache)
   :store (a/new-store)})

(defn- current-world [s] (:world (get @(:worlds s) @(:current s))))
(defn- current-root [s] (w/snapshot (current-world s)))

;; ---------------------------------------------------------------------------
;; printing
;; ---------------------------------------------------------------------------

(defn print-value
  "The printed form of a Klara value. Closures print as #<fn>, code
  values as Klara source (klara.code)."
  [v]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (if (instance? Throwable v)
      (str "#<" (.getSimpleName (class v)) " " (pr-str (ex-message v)) ">")
      (pr-str v))))

(defn- strip-prefix [msg]
  (some-> msg (str/replace #"^(klara|expand|define!)(\.[a-z]+)?: " "")))

(defn error-kind
  "[kind message] of a throwable, for `!! kind: message`."
  [^Throwable t]
  (let [data (ex-data t)
        msg (or (ex-message t) (str t))
        k (:klara/error data)]
    (cond
      (keyword? k) [(name k) (strip-prefix msg)]
      (str/starts-with? msg "expand:") ["expand" (strip-prefix msg)]
      (:klara/read data) ["read" msg]
      (contains? data :klara/exn) ["exn" (str "uncaught " (print-value (:klara/exn data)))]
      (str/starts-with? msg "klara") ["eval" (strip-prefix msg)]
      (instance? clojure.lang.ExceptionInfo t) ["ex-info" msg]
      :else [(.getSimpleName (class t)) msg])))

(defn format-error [t]
  (let [[k m] (error-kind t)] (str "!! " k ": " m)))

;; ---------------------------------------------------------------------------
;; evaluation of one top-level form
;; ---------------------------------------------------------------------------

(defn- def-form? [form]
  (and (seq? form) (contains? '#{def defmacro defsyntax defsyntax-class} (first form))))

(defn- define [s form]
  (let [wo (current-world s)
        {:keys [name]} (binding [ev/*fiber* (w/fiber wo)] (d/define! wo form))
        rep (d/invalidate! wo name)
        line (fn [k] (when-let [xs (seq (get rep k))]
                       (str ";; " (clojure.core/name k) ": " (str/join " " xs))))]
    (str/join "\n" (remove nil? [(str "#'" name) (line :stale) (line :cutoff)]))))

(defn- eval-form
  "Evaluate form against the current world's newest root, in a fiber
  pinned there (so :world/* operations act on the current world)."
  [s form]
  (let [fib (w/fiber (current-world s))
        root (w/basis fib)]
    (ev/run (x/expand-expr form root) {:basis root :fiber fib})))

(defn- eval-top-form
  "A top-level form: (def ..)/(defmacro ..) are published; anything else
  is expanded ONCE, and published if it expanded to a definition (defn
  and other def-producing macros), else evaluated in a fiber."
  [s form]
  (if (def-form? form)
    (define s form)
    (let [fib (w/fiber (current-world s))
          root (w/basis fib)
          res (x/expand-recorded form root)]
      (if (contains? #{:def :macro} (:kind res))
        (define s form)
        (print-value (ev/run (:term res) {:basis root :fiber fib}))))))

(defn- pretty [form]
  (str/trimr (with-out-str
               (binding [pp/*print-right-margin* 72 *print-meta* false]
                 (pp/with-pprint-dispatch pp/code-dispatch (pp/pprint form))))))

(def help-text
  (str/join "\n"
            [":repl/world            definitions of the current world, with versions"
             ":repl/basis            current world name and root version"
             ":repl/fork <name>      fork the current world as <name> and switch to it"
             ":repl/switch <name>    switch to world <name>"
             ":repl/expand <form>    show the core term of <form>, printed as source"
             ":repl/code <form>      evaluate <form> to a code value and pretty-print it"
             ":repl/compile <sym>     compile and install a definition"
             ":repl/compiled          list installed executables"
             ":repl/help             this list"]))

(defn- world-listing [s]
  (let [root (current-root s)
        defs (sort-by key (:defs root))]
    (if (empty? defs)
      ";; no definitions"
      (str/join "\n"
                (for [[sym e] defs]
                  (str sym " " (clojure.core/name (:kind e)) " v" (:version e)
                       (when (> (count (:history e)) 1) (str " (" (count (:history e)) " versions)"))
                       (when (w/pending? root e) " pending")))))))

(defn- basis-line [s]
  (let [nm @(:current s)
        {:keys [parent]} (get @(:worlds s) nm)]
    (str nm " v" (:version (current-root s))
         (when parent (str " (forked from " parent ")")))))

(defn- fork! [s nm]
  (let [nm (str nm)]
    (when (contains? @(:worlds s) nm)
      (throw (ex-info (str "a world named " nm " exists") {:klara/error :repl})))
    (let [from @(:current s)]
      (swap! (:worlds s) assoc nm {:world (w/fork (current-world s)) :parent from})
      (reset! (:current s) nm)
      (str "forked " from " -> " nm))))

(defn- switch! [s nm]
  (let [nm (str nm)]
    (when-not (contains? @(:worlds s) nm)
      (throw (ex-info (str "no world named " nm) {:klara/error :repl})))
    (reset! (:current s) nm)
    (str "switched to " nm)))

(def ^:private commands-with-arg #{:repl/fork :repl/switch :repl/expand :repl/code :repl/compile})

(defn- command?
  "REPL commands are keywords in the `repl` namespace, following clojure.main's
  :repl/quit; every other keyword is an ordinary value and evaluates to itself."
  [form]
  (and (keyword? form) (= "repl" (namespace form))))

(defn- run-command [s cmd arg]
  (case cmd
    :repl/compile (let [exe (compiler/compile-def (current-world s) arg {})]
                    (stage/install! (:cache s) exe)
                    (str ";; compiled " arg ": "
                         (str/join " -> " (map (comp name :pass) (:pass-log exe)))
                         "\n;; guards " (count (:guards exe))
                         "; allocations removed " (:allocations-removed exe)))
    :repl/compiled (let [es (sort-by (juxt :name :code-id) (stage/executables (:cache s)))]
                     (if (seq es)
                       (str/join "\n" (map #(str (:name %) " :tested") es))
                       ";; no compiled executables"))
    :repl/help help-text
    :repl/world (world-listing s)
    :repl/basis (basis-line s)
    :repl/fork (fork! s arg)
    :repl/switch (switch! s arg)
    :repl/expand (if (def-form? arg)
              (let [res (x/expand-recorded arg (current-root s))]
                (str "(" (first arg) " " (:name res) " "
                     (print-value (code/core->form (:term res))) ")"))
              (print-value (code/core->form (x/expand-expr arg (current-root s)))))
    :repl/code (let [v (eval-form s arg)]
            (if (code/code? v)
              (pretty (code/code->form v))
              (throw (ex-info (str ":repl/code expects a code value, got " (print-value v))
                              {:klara/error :repl}))))
    (throw (ex-info (str "unknown command " cmd " (try :repl/help)") {:klara/error :repl}))))

(defn- eval-top
  "Evaluate one top-level form (or command); returns the printed output."
  [s form arg]
  (let [out (java.io.StringWriter.)
        res (binding [*out* out a/*store* (:store s)]
              (try
                (stage/with-cache (:cache s)
                 (cond
                  (command? form) (run-command s form arg)
                  :else (eval-top-form s form)))
                (catch Throwable t (format-error t))))
        printed (str out)]
    (str/join "\n" (remove str/blank? [(str/trimr printed) res]))))

;; ---------------------------------------------------------------------------
;; reading
;; ---------------------------------------------------------------------------

(def ^:private eof (Object.))

(def reader-features
  "Reader-conditional features Klara answers to. The JVM reader always adds
  :clj (the platform feature), so in a .cljc form a :klara branch must come
  before a :clj branch to be chosen; :clj branches serve as the fallback
  while Klara is hosted on the JVM."
  #{:klara})

(defn- read-form [rdr]
  (try
    (binding [*read-eval* false
              *ns* (create-ns 'klara.user)]
      (read {:eof eof :read-cond :allow :features reader-features} rdr))
    (catch Throwable t
      (throw (ex-info (or (ex-message (or (.getCause t) t)) (str t)) {:klara/read true})))))

(defn eval-reader
  "Read and evaluate every form from rdr; calls emit with each output."
  [s rdr emit]
  (loop []
    (let [form (try (read-form rdr) (catch Throwable t t))]
      (cond
        (identical? eof form) nil
        (instance? Throwable form) (emit (format-error form))
        :else
        (let [arg (when (contains? commands-with-arg form)
                    (let [a (try (read-form rdr) (catch Throwable t t))]
                      (cond (identical? eof a) ::missing
                            (instance? Throwable a) a
                            :else a)))]
          (cond
            (= ::missing arg) (emit (str "!! repl: " form " needs an argument"))
            (instance? Throwable arg) (emit (format-error arg))
            :else (do (emit (eval-top s form arg)) (recur))))))))

(defn eval-string
  "Evaluate the forms in string text in session s; returns everything
  printed, lines joined by newlines."
  [s text]
  (let [outs (atom [])]
    (eval-reader s (LineNumberingPushbackReader. (StringReader. text))
                 #(swap! outs conj %))
    (str/join "\n" (remove str/blank? @outs))))

;; ---------------------------------------------------------------------------
;; interactive loop
;; ---------------------------------------------------------------------------

(defn- skip-line [^LineNumberingPushbackReader rdr]
  (loop [] (let [c (.read rdr)] (when-not (or (= c -1) (= c (int \newline))) (recur)))))

(defn repl
  "Interactive loop on *in* / *out*."
  []
  (let [s (session)
        rdr (LineNumberingPushbackReader. (java.io.InputStreamReader. System/in))]
    (println "Klara REPL over T0. :repl/help lists commands; Ctrl-D exits.")
    (loop []
      (print "k=> ") (flush)
      (let [form (try (read-form rdr) (catch Throwable t t))]
        (cond
          (identical? eof form) (println)
          (instance? Throwable form) (do (println (format-error form)) (skip-line rdr) (recur))
          :else
          (let [arg (when (contains? commands-with-arg form)
                      (try (read-form rdr) (catch Throwable t t)))]
            (cond
              (identical? eof arg) (println)
              (instance? Throwable arg) (do (println (format-error arg)) (skip-line rdr) (recur))
              :else (let [o (eval-top s form arg)]
                      (when-not (str/blank? o) (println o))
                      (recur)))))))))

(defn -main [& _] (repl) (shutdown-agents))
