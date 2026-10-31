(ns klara.local-optimizer)

;; Read-only compiler descriptions contain node indices and binding identities.
;; A validated self-tail loop's function is marked transparent by the adapter.
(defn uses [nodes start binding arity]
  (loop [i 0 work [[start false]] calls 0]
    (if (< i (count work))
      (let [task (nth work i) node (nth nodes (nth task 0)) nested (nth task 1)
            op (get node :op)
            direct (if (= op :app)
                     (if (= binding (get node :callee))
                       (if nested false (= arity (get node :arity))) false) false)
            blocked (if (= op :fn) (if (get node :transparent?) nested true) nested)
            children (get node :children)]
        (if (if (= op :local) (= binding (get node :binding)) false)
          {:safe? false :calls calls}
          (let [next-work (loop [j (if direct 1 0) result work]
                            (if (< j (count children))
                              (recur (inc j) (conj result [(nth children j) blocked])) result))]
            (recur (inc i) next-work (if direct (inc calls) calls)))))
      {:safe? true :calls calls})))

;; Generate a pure planner specialized to a small policy choice. Staging runs
;; while this module loads; the residual planner contains no staging effects.
(defn planner-code [minimum-calls]
  (code
    (fn [request]
      (let [nodes (get request :nodes) candidates (get request :candidates)]
        (loop [i 0 selected []]
          (if (< i (count candidates))
            (let [at (nth candidates i) node (nth nodes at)
                  function (nth nodes (get node :init))
                  result (klara.local-optimizer/uses nodes (get node :body)
                           (get node :binding) (get function :arity))]
              (recur (inc i)
                     (if (get result :safe?)
                       (if (>= (get result :calls) (esc (lift minimum-calls)))
                         (conj selected at) selected)
                       selected)))
            {:source-id (get request :source-id) :bindings selected}))))))

(def planner (run (planner-code 1)))

;; Before-use and later runtime optimization share this operation. The worker
;; prepares in an isolated fork; installation happens after leaving that fork.
(defn prepare-code [source]
  (let [candidate (fork [job (perform :stage/prepare source
                              {:backend :baseline
                               :local-call-planner 'klara.local-optimizer/planner})]
                    (adopt! job))]
    (perform :stage/install candidate)))
