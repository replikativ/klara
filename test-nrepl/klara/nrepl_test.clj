(ns klara.nrepl-test
  (:require [clojure.test :refer [deftest is]] [nrepl.core :as nrepl]
            [nrepl.server :as server] [klara.nrepl :as guest]))

(deftest guest-protocol-keeps-sessions-and-loads-world-code
  (let [s (guest/start! {:source-roots ["examples/compat"]})]
    (try
      (with-open [connection (nrepl/connect :host "127.0.0.1" :port (:port s))]
        (let [client (nrepl/client connection 30000)
              request (fn [msg] (first (doall (nrepl/message client msg))))
              session (:new-session (request {:op "clone"}))
              other (:new-session (request {:op "clone"}))
              send (fn [msg] (request (assoc msg :session session)))
              evaluate (fn [code] (send {:op "eval" :code code}))]
          (is (= "klara" (get-in (send {:op "describe"}) [:aux :language])))
          (is (= "nil\n#'agent.demo/f\n42"
                 (:value (evaluate "(ns agent.demo) (defn f [x] (+ x 1)) (f 41)"))))
          (is (= "8" (:value (evaluate "(f 7)"))))
          (is (contains? (set (:status (request {:op "eval" :session other :code "(agent.demo/f 1)"}))) "eval-error"))
          (is (nil? (ns-resolve (create-ns 'agent.demo) 'f)))
          (is (= "demo.pipeline"
                 (:ns (send {:op "load-file" :file (slurp "examples/compat/demo/pipeline.cljc")}))))
          (is (= "27" (:value (evaluate "(kernel 4)"))))
          (is (contains? (set (:status (evaluate "(binding [*print-length* 1] 1)"))) "eval-error"))))
      (finally (server/stop-server s)))))
