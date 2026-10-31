(ns klara.nrepl
  "Trusted developer nREPL evaluating guest Klara without implicit host eval.
   Explicit host interop remains available; this endpoint is not a sandbox.
   Optional dependency. Sessions serialize requests; clone starts a fresh world.
   Interrupt/completion/debug middleware are not yet implemented."
  (:require [nrepl.server :as server] [nrepl.transport :as transport]
            [nrepl.misc :refer [response-for]]
            [klara.repl :as repl] [klara.load :as loader]
            [klara.compile.staged]
            [klara.authority :as authority] [klara.stage :as stage]))

(defn handler [options]
  (let [sessions (atom {})
        ops ["clone" "close" "ls-sessions" "describe" "eval" "load-file"]]
    (fn [{:keys [op session code file file-path transport] :as msg}]
      (let [send #(transport/send transport (response-for msg %))]
        (case op
          "clone" (let [id (str (java.util.UUID/randomUUID))]
                    (swap! sessions assoc id (repl/session options))
                    (send {:new-session id :status #{:done}}))
          "close" (do (swap! sessions dissoc session) (send {:status #{:done :session-closed}}))
          "ls-sessions" (send {:sessions (vec (keys @sessions)) :status #{:done}})
          "describe" (send {:ops (zipmap ops (repeat {})) :aux {:language "klara" :clone "fresh-world"}
                            :versions {"klara" {"version-string" "prototype"}} :status #{:done}})
          (if-not (contains? #{"eval" "load-file"} op)
            (send {:status #{:error :unknown-op :done}})
            (if-let [s (if session (get @sessions session) (repl/session options))]
              (locking s
                (try
                  (if (= "eval" op)
                    (let [{:keys [output errors]} (repl/eval-response s code)]
                      (send (merge {:ns (str (or @(:namespace s) 'user)) :status #{:done}}
                                   (if (seq errors) {:err output :ex (ffirst errors) :status #{:eval-error :done}}
                                     {:value output}))))
                    (let [result (binding [authority/*store* (:store s)]
                                   (stage/with-cache (:cache s)
                                     (loader/load-string! (repl/current-world s) file
                                       (assoc (repl/load-options s)
                                              :path file-path :namespace @(:namespace s)))))]
                      (reset! (:namespace s) (:namespace result))
                      (send {:value (repl/print-value (:value result))
                             :ns (str (or (:namespace result) 'user)) :status #{:done}})))
                  (catch Throwable t
                    (send {:err (repl/format-error t) :ex (.getName (class t)) :status #{:eval-error :done}}))))
              (send {:status #{:error :unknown-session :done}}))))))))

(defn start! [options]
  (server/start-server :bind "127.0.0.1" :port (:port options 0) :handler (handler options)))

(defn -main [& args]
  (let [options (loop [args args result {:source-roots ["examples/compat"]}]
                  (if-let [[option value & more] (seq args)]
                    (case option
                      "--port" (recur more (assoc result :port (Integer/parseInt value)))
                      "--source-root" (recur more (update result :source-roots conj value))
                      "--prepare" (if (contains? #{"off" "baseline"} value)
                                    (recur more (assoc result :prepare (keyword value)))
                                    (throw (ex-info "expected off or baseline" {:value value})))
                      (throw (ex-info "expected --port, --source-root or --prepare" {:option option}))) result))
        s (start! options)]
    (spit ".nrepl-port" (:port s))
    (println "Klara nREPL listening on 127.0.0.1 port" (:port s))
    (.addShutdownHook (Runtime/getRuntime) (Thread. #(server/stop-server s)))
    @(promise)))
