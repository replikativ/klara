(ns klara.compile.budget
  "Preparation work counters, not wall-clock deadlines. Children spend their
   ancestor's allowance too; failed requests retain all prior charges.")

(def session-limits {:work 131072 :emissions 16 :bytes 1048576})
(def file-limits {:work 32768 :emissions 4 :bytes 262144})
(def definition-limits {:nodes 512 :depth 64 :literal-bytes 4096})
(def units #{:work :emissions :bytes})

(defn validate-limits! [limits allowed]
  (when-not (and (map? limits) (every? allowed (keys limits))
                 (every? #(and (integer? %) (<= 0 % Long/MAX_VALUE)) (vals limits)))
    (throw (ex-info "invalid preparation limits" {:reason :invalid-budget})))
  limits)

(defn budget
  ([] (budget session-limits nil))
  ([limits] (budget limits nil))
  ([limits parent] (validate-limits! limits units)
   {:limits limits :used (atom {}) :parent parent}))

(defn exhausted! [unit]
  (throw (ex-info "preparation budget exhausted" {:reason :budget-exhausted :unit unit})))

(defn charge!
  "Charge ancestors first. A declined child request still spends ancestor
   work; counters never reset on declines or dependency traversal."
  [b unit amount]
  (when-not (and (units unit) (integer? amount) (<= 0 amount Long/MAX_VALUE))
    (throw (ex-info "invalid preparation charge" {:reason :invalid-budget})))
  (when b
    (when-let [parent (:parent b)] (charge! parent unit amount))
    (swap! (:used b)
           (fn [used]
             (let [n (+ (get used unit 0) amount)]
               (when (> n (get (:limits b) unit Long/MAX_VALUE)) (exhausted! unit))
               (assoc used unit n)))))
  nil)

(defn usage [b] (when b @(:used b)))
