(ns klara.formal.dev
  "REPL helper for proof development: evaluate a proof file form by form,
  skipping constants that are already declared, and report the first failure.
  ansatz rejects redeclaration, so this avoids reloading the whole stack.")

(defn load-forms!
  [path]
  (let [r (clojure.lang.LineNumberingPushbackReader. (clojure.java.io/reader path))
        ns-form (read r)]
    (eval ns-form)
    (loop [ok 0 skipped 0]
      (let [form (read {:eof ::eof} r)]
        (if (= ::eof form)
          {:ok ok :skipped skipped}
          (let [res (try (eval form) :ok
                         (catch Throwable e
                           (let [msg (loop [e e] (if (.getCause e) (recur (.getCause e)) (.getMessage e)))]
                             (if (re-find #"already declared" (str msg)) :skipped
                                 {:failed (second form) :message (subs (str msg) 0 (min 2500 (count (str msg))))}))))]
            (cond (= :ok res) (recur (inc ok) skipped)
                  (= :skipped res) (recur ok (inc skipped))
                  :else (assoc res :ok ok :skipped skipped))))))))
