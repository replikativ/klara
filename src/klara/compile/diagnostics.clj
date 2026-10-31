(ns klara.compile.diagnostics
  "Opt-in preparation phase attribution. No source execution, logging service
   or event accumulation on ordinary calls; nested durations are inclusive.")

(def ^:dynamic *events* nil)
(def maximum-events 512)

(defn timed [phase details f]
  (let [start (System/nanoTime) status (volatile! :completed)]
    (try (f)
         (catch Throwable e (vreset! status :failed) (throw e))
         (finally
           (let [event {:phase phase :details details :status @status
                        :elapsed-ns (- (System/nanoTime) start)}]
             (swap! *events* (fn [state]
                              (if (< (count (:events state)) maximum-events)
                                (update state :events conj event)
                                (update state :dropped inc)))))))))

(defmacro phase [name details & body]
  `(if *events* (timed ~name ~details (fn [] ~@body)) (do ~@body)))

(defn capture [f]
  (let [events (atom {:events [] :dropped 0})]
    (binding [*events* events]
      (let [value (f)] {:value value :diagnostics @events}))))
