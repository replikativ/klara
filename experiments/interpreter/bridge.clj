(ns interpreter.bridge
  "Experimental one-way bridge from private pure CEK state to existing T0.
   This is trusted hosted code, not a general snapshot or authority interface."
  (:refer-clojure :exclude [prepare])
  (:require [interpreter.mutable :as m] [klara.core :as core]
            [klara.eval :as ev] [klara.world :as w])
  (:import [interpreter.mutable Node PrivateClosure]
           [klara.eval Closure]
           [java.util IdentityHashMap Collections Map ArrayList]))

(defn- reject! [reason] (throw (ex-info "CEK bridge: declined" {:bridge/decline reason})))

(defn- check-primitives! [roots]
  (doseq [[name f] roots]
    (when-not (identical? f (get core/prims name)) (reject! :primitive-context))))

(defn prepare
  "Prepare a closed pure entry and retain exact original Core nodes, including
   metadata. basis is explicit and pinned; open/mixed-world closures are deferred."
  ([term] (prepare term {}))
  ([term {:keys [basis] :or {basis w/empty-root} :as options}]
   (when (seq (dissoc options :basis)) (reject! :unsupported-context))
   (let [origins (IdentityHashMap.)
         ;; Check actual anchors before preparation can evaluate initializers.
         _ (check-primitives! (m/primitive-roots))
         entry (m/prepare term origins)
         names (into #{} (keep #(when (= :prim (:op %)) (:name %))) (.values origins))
         roots (select-keys (m/primitive-roots) names)]
     {:entry entry :source term :source-id (core/code-id term)
      :basis basis :mint basis :origins (Collections/unmodifiableMap origins)
      :primitive-roots roots})))

(defn- capsule [artifact machine context]
  {:artifact artifact :context context :life (atom {:status :paused :machine machine})})

(defn start
  "A new call observes the caller's current decimal context. A pause retains
   this immutable setting for subsequent private or T0 resumption."
  [artifact args]
  (check-primitives! (:primitive-roots artifact))
  (capsule artifact ((or (get-in artifact [:engine :start]) m/start) (:entry artifact) args)
           {:math-context *math-context*}))

(defn status [capsule] (:status @(:life capsule)))

(defn- owned-machine [capsule]
  (let [{:keys [status machine]} @(:life capsule)]
    (when-not (#{:paused :done} status) (reject! :not-owned))
    machine))

(defn advance! [capsule fuel]
  (locking (:life capsule)
    (let [machine (owned-machine capsule)]
      (check-primitives! (get-in capsule [:artifact :primitive-roots]))
      (swap! (:life capsule) assoc :status :advancing)
      (try
        (let [status (binding [*math-context* (get-in capsule [:context :math-context])]
                       ((or (get-in capsule [:artifact :engine :advance!]) m/advance!) machine fuel))]
          (swap! (:life capsule) assoc :status status)
          status)
        (catch Throwable t
          (reset! (:life capsule) {:status :failed})
          (throw t))))))

(defn freeze [capsule]
  (locking (:life capsule)
    {:artifact (:artifact capsule) :context (:context capsule)
     :frozen ((or (get-in capsule [:artifact :engine :freeze]) m/freeze) (owned-machine capsule))}))

(defn thaw [snapshot]
  (capsule (:artifact snapshot)
           ((or (get-in snapshot [:artifact :engine :thaw]) m/thaw) (:frozen snapshot))
           (:context snapshot)))

(defn result!
  "Return admitted immutable data from a completed call without reconstructing
   CEK state. Returning consumes the controller lease, as transfer does."
  [capsule]
  (locking (:life capsule)
    (let [machine (owned-machine capsule)]
      (when-not (= :done (status capsule)) (reject! :not-done))
      (let [v ((or (get-in capsule [:artifact :engine :result]) m/result) machine)]
        (when-not (m/data? v)
          (reset! (:life capsule) {:status :failed})
          (reject! :output))
        (reset! (:life capsule) {:status :returned})
        v))))

(defn invoke
  "Common complete-call interface for experimental engines. Reconstruction is
   needed only for an explicit transfer; ordinary completion returns data."
  [artifact & args]
  (let [c (start artifact args)]
    (while (= :paused (advance! c 100000)))
    (result! c)))

(defn- reconstruct
  "No guest code is run. Memoized closure shells and shared delayed capture
   vectors preserve aliases and recursive groups without exposing live arrays."
  [artifact {:keys [registers frames]}]
  (let [closures (IdentityHashMap.) captures (IdentityHashMap.)
        ^Map origins (:origins artifact) basis (:basis artifact) mint (:mint artifact)
        ^objects r registers ^ArrayList frames frames]
    (letfn [(origin [node]
              (or (.get origins node) (reject! :unknown-code)))
            (value [v]
              (cond
                (instance? PrivateClosure v)
                (or (.get closures v)
                    (let [^PrivateClosure v v ^objects array (.-captured v)
                          existing (.get captures array)
                          promise (or existing (promise))
                          _ (when-not existing (.put captures array promise))
                          c (Closure. (origin (.-term v)) (delay @promise) mint)]
                      (.put closures v c)
                      (when-not existing
                        (deliver promise (mapv #(value (aget array %)) (range (alength array)))))
                      c))
                (m/data? v) v
                :else (reject! :unsupported-value)))
            (environment [^objects array size]
              {:locals (mapv #(value (aget array %)) (range size)) :basis basis :mint mint})
            (frame [i]
              (let [^objects f (.get frames (int i)) tag (long (aget f 0))
                    node (origin (aget f 1)) env (environment (aget f 2) (long (aget f 3)))]
                (case tag
                  0 {:tag :let :body node :env env}
                  1 {:tag :if :node node :env env}
                  2 (let [vals (mapv value (aget f 4))
                          terms (case (:op node)
                                  :app (cons (:fn node) (:args node))
                                  :prim (:args node)
                                  (reject! :operand-frame))]
                      {:tag :list :node node :env env :vals vals
                       :todo (drop (inc (count vals)) terms)})
                  (reject! :frame-kind))))]
      (let [mode (long (aget r 0))
            env (environment (aget r 2) (long (aget r 3)))
            ;; Private frames are bottom-first; T0's list is top-first.
            k (reduce (fn [k i] (conj k (frame i))) '() (range (long (aget r 4))))]
        (case mode
          0 [:eval (origin (aget r 1)) env k]
          1 [:ret (value (aget r 1)) env k]
          2 [:finish (origin (aget r 1)) (mapv value (aget r 6)) env k]
          (reject! :mode))))))

(defn transfer!
  "Relinquish one capsule to T0. Reconstruct before consuming ownership, so a
   rejected transfer leaves the paused capsule available for inspection.
   This is an API lease, not a general affine/authority proof."
  [capsule]
  (locking (:life capsule)
    (let [machine (owned-machine capsule)
          artifact (:artifact capsule)]
      (check-primitives! (:primitive-roots artifact))
      (let [project (get-in artifact [:engine :project] identity)
            state (reconstruct artifact (project machine))]
        (reset! (:life capsule) {:status :transferred})
        {:state state :artifact artifact :context (:context capsule)
         :life (atom :ready)}))))

(defn resume!
  "Run a transferred state once, under its entry context, without compiler
   hooks. Concurrent arbitrary host primitive redefinition is outside this
   contract. Only immutable data outputs are admitted by this controller."
  ([transfer] (resume! transfer true))
  ([transfer reference?]
   (locking (:life transfer)
     (when-not (= :ready @(:life transfer)) (reject! :already-resumed))
     (check-primitives! (get-in transfer [:artifact :primitive-roots]))
     (reset! (:life transfer) :running)
     (try
       (let [v (binding [*math-context* (get-in transfer [:context :math-context])
                         ev/*reference-driver* reference? ev/*entry-hook* nil
                         ev/*direct-hook* nil ev/*context-hook* nil
                         ev/*basis* (get-in transfer [:artifact :basis])
                         ev/*mint* (get-in transfer [:artifact :mint]) ev/*fiber* nil ev/*outer-k* '()]
                 (ev/drive (:state transfer)))]
         (when-not (m/data? v) (reject! :output))
         (reset! (:life transfer) :done)
         v)
       (catch Throwable t (reset! (:life transfer) :failed) (throw t))))))
