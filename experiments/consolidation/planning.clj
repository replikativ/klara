(ns consolidation.planning
  "Guest planning over existing checked recipes. A restricted pure T0 runner
   bounds guest transitions; host preparation is measured, not preempted."
  (:require [clojure.java.io :as io] [clojure.set :as set]
            [klara.core :as c] [klara.code :as code] [klara.defs :as d]
            [klara.world :as w] [klara.expand :as expand] [klara.eval :as ev] [klara.authority :as authority]
            [klara.compile.staged :as staged] [klara.stage :as stage]
            [consolidation.checked-pipeline :as pipeline] [proof-staging :as ps]))

(def prims '#{+ - * inc dec < > <= >= = not= not zero? pos? neg? identity
              vector hash-map hash-set first second rest next empty? count nth get assoc dissoc conj})
(def host-symbols '#{clojure.core/subvec clojure.core/get-in clojure.core/contains?})
(def core-roots c/prims)
(def host-roots (into {} (map (fn [sym] [sym @(resolve sym)]) host-symbols)))
(defn- fail! [check] (throw (ex-info "planner boundary rejected" {:reason :planner :check check})))

(defn load-world []
  (let [world (w/make-world)]
    (with-open [reader (java.io.PushbackReader. (io/reader "examples/staging/15-planned-jit.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} reader)))]
        (d/define! world form))) world))

(defn problem
  ([coefficients domain] (problem coefficients domain
     {:numeric-ns 1000000 :fusion-ns 1000000 :emit-ns 20000000 :guard-ns 100
      :run-ns {:source 100000 :numeric 90000 :stream 20000 :both 10000}}))
  ([coefficients domain estimates]
   (let [codes (ps/proposals coefficients)]
     {:coefficients coefficients :domain domain :codes codes
      :ids (into {} (map (fn [[key value]] [key (c/code-id (ps/core-term value))]) codes))
      :semantics :bounded-nat-vector-v1 :observation :successful-pure-scalar
      :interface {:arity 1 :representation :persistent-vector}
      :estimates estimates :estimate-provenance :supplied-not-a-measured-forecast})))

(defn- inert? [value depth]
  (and (pos? depth)
       (cond
         (or (nil? value) (instance? Long value) (boolean? value) (keyword? value) (symbol? value)) true
         (string? value) (<= (count value) 4096)
         (code/code? value) (and (code/closed? value)
                                 (<= (count (tree-seq map? c/children (ps/core-term value))) 2048))
         (= clojure.lang.PersistentVector (class value))
         (and (<= (count value) 128) (every? #(inert? % (dec depth)) value))
         (#{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class value))
         (and (<= (count value) 128) (every? #(inert? % (dec depth)) (mapcat identity value)))
         :else false)))

(defn- validate-policy! [root symbol]
  (loop [todo [symbol] checked #{}]
    (if-let [sym (peek todo)]
      (if (contains? checked sym) (recur (pop todo) checked)
        (let [entry (w/entry* root sym) term (:code entry)]
          (when-not (and entry (not (w/pending? root entry)) (= :fn (:op term))
                         (ev/closure? (:value entry)) (empty? (ev/closure-locals (:value entry)))) (fail! :source-backed-policy))
          (let [references (atom #{})]
            (doseq [node (tree-seq map? c/children term)]
              (case (:op node)
                (:fn :app :local :let :if :letrec) nil
                :quote (when-not (inert? (:datum node) 16) (fail! :literal))
                :prim (when-not (contains? prims (:name node)) (fail! :primitive))
                :resolve (swap! references conj (:id node))
                :perform (when-not (and (nil? (:target node)) (= :host/call (:name node))
                                        (= :quote (get-in node [:args 0 :op]))
                                        (contains? host-symbols (get-in node [:args 0 :datum])))
                           (fail! :effect))
                (fail! :syntax)))
            (recur (into (pop todo) (set/difference @references checked)) (conj checked sym)))))
      checked)))

(defn invoke-policy
  "Execute only source-backed pure policy definitions with inert inputs and
   reference primitive roots. Fuel counts actual T0 transitions. There are no
   guest authority frames to abandon; this is not a general effectful runner."
  [root policy args fuel]
  (when-not (and (instance? Long fuel) (<= 0 fuel 1000000) (inert? args 24)) (fail! :inputs))
  (when-not (and (identical? core-roots c/prims)
                 (every? (fn [[sym value]] (identical? value @(resolve sym))) host-roots)) (fail! :host-root))
  (let [dependencies (validate-policy! root policy)
        term (apply c/app (c/resolve* policy) (map c/quote* args))]
    (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
              ev/*outer-k* [] ev/*fiber* nil ev/*basis* root
              authority/*store* (authority/new-store)]
      (loop [state [:eval term {:locals [] :basis root :mint root} '()] remaining fuel]
        (if (and (= :ret (first state)) (empty? (nth state 3)))
          {:status :completed :value (second state) :transitions (- fuel remaining) :dependencies dependencies}
          (if (zero? remaining)
            {:status :pending :reason :transition-budget :transitions fuel :dependencies dependencies}
            (recur (ev/step-state state) (dec remaining))))))))

(def preparation-core
  ;; Expanded against the empty seed root, independent of mutable guest macros.
  (expand/expand-expr
    '(fn [request] (fork [job (perform :stage/prepare-checked request)] (adopt! job))) w/empty-root))

(defn prepare-plan
  "Fixed cold boundary. A policy may propose, but cannot select the validator
   or change the reference subject/domain of the job. Record failed work too."
  [root problem plan]
  (let [start (System/nanoTime)]
    (try
      (when-not (and (inert? plan 24) (= :prepare (:action plan))
                     (= (get-in problem [:ids :source]) (c/code-id (ps/core-term (:source plan))))
                     (= (:domain problem) (:domain plan))
                     (every? #(instance? Long (get-in plan [:domain %])) [:max-count :max-x]))
        (fail! :reference-subject))
      (let [request (select-keys plan [:source :targets :steps :domain :executor])
            candidate (binding [authority/*store* (authority/new-store)
                                ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
                                ev/*outer-k* [] ev/*fiber* nil]
                        (ev/call-value (ev/run preparation-core {:basis root}) [request]))]
        (if (instance? klara.compile.staged.Prepared candidate)
          {:status :prepared :candidate candidate :elapsed-ns (- (System/nanoTime) start)
           :request request :preparation-isolation :authority-fork :fork-exited true
           :evidence :existing-checked-chain-with-tested-runtime-bridges}
          {:status :declined :reason (:reason candidate) :elapsed-ns (- (System/nanoTime) start)}))
      (catch clojure.lang.ExceptionInfo ex
        {:status :declined :reason (or (:check (ex-data ex)) (:reason (ex-data ex)))
         :elapsed-ns (- (System/nanoTime) start)}))))

(defn controller [budget-ns attempts]
  {:remaining-ns budget-ns :remaining-attempts attempts :history [] :attempted #{} :incumbent nil})

(defn- attempt-key [plan]
  (try [(c/code-id (ps/core-term (:source plan)))
        (mapv #(c/code-id (ps/core-term %)) (:targets plan))
        (:steps plan) (:domain plan) (:executor plan)]
       (catch Exception _ [:invalid-proposal])))

(defn invest
  "Planner and compilation are synchronous. Actual total work charges the
   controller after completion; host compilation has no wall-clock preemption."
  [cache reference-root policy-root policy problem profile limits state]
  (if (or (<= (:remaining-ns state) 0) (<= (:remaining-attempts state) 0))
    {:status :stopped :reason :investment-budget :controller state}
    (let [started (System/nanoTime)
          decision (invoke-policy policy-root policy [problem profile (assoc limits :preparation-ns (:remaining-ns state))]
                                  (:transition-fuel limits))
          planning-ns (- (System/nanoTime) started)
          plan (:value decision) key (when (= :prepare (:action plan)) (attempt-key plan))
          repeated (contains? (:attempted state) key)
          preparation (when (and key (not repeated)) (prepare-plan reference-root problem plan))
          publication-start (System/nanoTime)
          publication (when (= :prepared (:status preparation))
                        (try (staged/install! cache reference-root (:candidate preparation))
                             (catch clojure.lang.ExceptionInfo ex {:status :declined :reason (:reason (ex-data ex))})))
          publication-ns (if publication (- (System/nanoTime) publication-start) 0)
          spent (- (System/nanoTime) started)
          status (cond repeated :stopped publication (:status publication) preparation (:status preparation)
                       (= :pending (:status decision)) :pending (= :stop (:action plan)) :stopped :else :declined)
          reason (cond repeated :already-attempted (= :pending status) :transition-budget
                       publication (:reason publication) preparation (:reason preparation)
                       (= :stop (:action plan)) (or (:reason plan) :no-positive-benefit) :else :invalid-plan)
          entry {:policy-id (:code-id (w/entry* policy-root policy))
                 :action (:action plan) :node (:node plan) :steps (:steps plan)
                 :planning-ns planning-ns :preparation-ns (or (:elapsed-ns preparation) 0)
                 :publication-ns publication-ns :total-ns spent
                 :transitions (:transitions decision) :status status :reason reason}
          next-state (-> state (update :remaining-ns - spent)
                         (update :remaining-attempts #(if preparation (dec %) %))
                         (update :history conj entry)
                         (cond-> key (update :attempted conj key))
                         (cond-> (= :installed status) (assoc :incumbent (:code-id publication))))]
      {:status status :reason reason :plan plan :controller next-state :publication publication})))
