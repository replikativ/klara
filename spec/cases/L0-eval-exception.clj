;; rules: L0.eval.exception
;; expect: [1 "inner" [:finally :inner]]
(def log (atom []))
[(try (throw (ex-info "boom" {:x 1})) (catch clojure.lang.ExceptionInfo e (:x (ex-data e))) (finally (swap! log conj :finally)))
 (try (try (throw (ex-info "inner" {})) (finally (swap! log conj :inner))) (catch Exception e (.getMessage e)))
 @log]
