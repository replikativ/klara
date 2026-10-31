(ns interpreter.mutable
  "Experimental, thread-confined CEK storage for a closed pure Core fragment.
   No host effects, globals, staging, handlers, rest arguments or guest mutation.
   Snapshot/thaw is explicit; this is not installed as Klara's runtime."
  (:refer-clojure :exclude [run!])
  (:require [klara.core :as core])
  (:import [java.util ArrayList Arrays]))

(deftype Node [^long op ^long index ^long arity value a b c ^objects args])
(deftype PrivateClosure [term ^objects captured])
(deftype Frozen [registers frames])

(defn- put! [^objects array ^long index value]
  ;; The Object-typed value selects RT.aset(Object[], int, Object) without
  ;; reflective overload resolution for boxed machine registers/cursors.
  (aset array (int index) value))

(defn- decline [reason] (throw (ex-info "mutable CEK: unsupported" {:decline reason})))
(def ^:private scalar-classes
  #{Long Double Boolean String clojure.lang.Keyword clojure.lang.Symbol
    clojure.lang.BigInt clojure.lang.Ratio java.math.BigInteger java.math.BigDecimal})

(defn data? [v]
  (or (nil? v)
      (and (contains? scalar-classes (class v)) (nil? (meta v)))
      (and (or (= (class v) clojure.lang.PersistentVector)
               (= (class v) clojure.lang.APersistentVector$SubVector))
           (nil? (meta v)) (every? data? v))))

(def ^:private primitives
  (select-keys core/prims '[+ - * / inc dec < > <= >= = not not= zero? pos? neg?
                            quot rem mod identity vector assoc nth count first second]))

(defn primitive-data? [v]
  ;; Inputs and quotes have already been checked recursively. The closed
  ;; primitive family cannot introduce mutable host leaves into these vectors.
  (or (nil? v) (contains? scalar-classes (class v))
      (= (class v) clojure.lang.PersistentVector)
      (= (class v) clojure.lang.APersistentVector$SubVector)))

(defn- validate! [term]
  (case (:op term)
    :local nil
    :quote (when-not (data? (:datum term)) (decline :quoted-host-value))
    :fn (do (when (:rest? term) (decline :rest-arguments)) (validate! (:body term)))
    :let (do (validate! (:init term)) (validate! (:body term)))
    :if (doseq [t [(:test term) (:then term) (:else term)]] (validate! t))
    :letrec (do (doseq [t (:inits term)] (validate! t)) (validate! (:body term)))
    :app (do (validate! (:fn term)) (doseq [t (:args term)] (validate! t)))
    :prim (do (when-not (get primitives (:name term)) (decline :primitive))
              (doseq [t (:args term)] (validate! t)))
    (decline (:op term))))

(defn- predecode [term origins]
  (let [node (case (:op term)
    :quote (Node. 0 0 0 (:datum term) nil nil nil nil)
    :local (Node. 1 (:index term) 0 nil nil nil nil nil)
    :fn (Node. 2 0 (:arity term) nil (predecode (:body term) origins) nil nil nil)
    :let (Node. 3 0 0 nil (predecode (:init term) origins) (predecode (:body term) origins) nil nil)
    :if (Node. 4 0 0 nil (predecode (:test term) origins) (predecode (:then term) origins) (predecode (:else term) origins) nil)
    :letrec (Node. 5 0 0 nil (predecode (:body term) origins) nil nil (object-array (map #(predecode % origins) (:inits term))))
    :app (Node. 6 0 0 nil (predecode (:fn term) origins) nil nil (object-array (map #(predecode % origins) (:args term))))
    :prim (Node. 7 0 0 (:name term) nil nil nil (object-array (map #(predecode % origins) (:args term)))))]
    (when origins (.put ^java.util.Map origins node term))
    node))

(defn primitive-roots "Immutable host primitive anchors for experimental admission." [] primitives)

;; Registers: mode (0 eval / 1 return), control, locals array, lexical size,
;; stack depth, done?. Stack entries are reusable arrays:
;; tag (0 let / 1 if / 2 operands), node, locals, lexical size, values, next arg.
(defn- machine [term]
  {:registers (object-array [0 term (object-array 16) 0 0 false]) :frames (ArrayList.)})

(defn- grow ^objects [^objects locals size]
  (if (< size (alength locals)) locals
    (Arrays/copyOf locals (int (max (inc size) (* 2 (alength locals)))))))

(defn- push-frame! [^ArrayList frames depth tag node locals size]
  (let [^objects frame (if (< depth (.size frames)) (.get frames (int depth))
                         (let [f (object-array [nil nil nil nil (ArrayList.) nil])]
                           (.add frames f) f))]
    (put! frame 0 tag) (put! frame 1 node) (put! frame 2 locals) (put! frame 3 size)
    (.clear ^ArrayList (aget frame 4)) (put! frame 5 0)
    frame))

(defn- saved-array? [^ArrayList frames depth locals]
  (loop [i 0]
    (and (< i depth)
         (or (identical? locals (aget ^objects (.get frames (int i)) 2))
             (recur (inc i))))))

(defn- primitive! [name ^ArrayList values]
  (let [f (get primitives name)]
    ;; No general host call is allowed. Even an override introduced after
    ;; preparation must decline before it can execute.
    (when-not (identical? f (get core/prims name)) (decline :changed-primitive))
    (dotimes [i (.size values)]
      (when-not (primitive-data? (.get values i)) (decline :primitive-operands)))
    (case (.size values)
      0 (f)
      1 (f (.get values 0))
      2 (f (.get values 0) (.get values 1))
      3 (f (.get values 0) (.get values 1) (.get values 2))
      4 (f (.get values 0) (.get values 1) (.get values 2) (.get values 3))
      5 (f (.get values 0) (.get values 1) (.get values 2) (.get values 3) (.get values 4))
      (apply f (seq (.toArray values))))))

(defn advance!
  "Execute at most fuel CEK transitions. Caller owns the machine exclusively.
   Returns :paused or :done. Exceptions leave only this private machine dirty."
  [{:keys [registers frames]} fuel]
  (when-not (and (integer? fuel) (<= 0 fuel Long/MAX_VALUE)) (decline :fuel))
  (let [^objects registers registers ^ArrayList frames frames]
    (loop [mode (long (aget registers 0)) c (aget registers 1)
           locals (aget registers 2) size (long (aget registers 3))
           depth (long (aget registers 4)) fuel (long fuel)]
      (if (or (zero? fuel) (and (= mode 1) (zero? depth)))
        (let [done? (and (= mode 1) (zero? depth))]
          (put! registers 0 mode) (put! registers 1 c) (put! registers 2 locals)
          (put! registers 3 size) (put! registers 4 depth) (put! registers 5 done?)
          (if done? :done :paused))
        (let [fuel (dec fuel) ^objects locals locals]
          (if (zero? mode)
            (case (.-op ^Node c)
              0 (recur 1 (.-value ^Node c) locals size depth fuel)
              1 (recur 1 (aget locals (int (- size 1 (.-index ^Node c)))) locals size depth fuel)
              2 (recur 1 (PrivateClosure. c (Arrays/copyOf locals (int size))) locals size depth fuel)
              3 (do (push-frame! frames depth 0 (.-b ^Node c) locals size)
                    (recur 0 (.-a ^Node c) locals size (inc depth) fuel))
              4 (do (push-frame! frames depth 1 c locals size)
                    (recur 0 (.-a ^Node c) locals size (inc depth) fuel))
              5
              (let [^objects inits (.-args ^Node c) n (alength inits)
                    captured (Arrays/copyOf locals (int (+ size n)))
                    locals (grow locals (+ size n))]
                (dotimes [i n]
                  (let [cl (PrivateClosure. (aget inits i) captured)]
                    (put! captured (+ size i) cl) (put! locals (+ size i) cl)))
                (recur 0 (.-a ^Node c) locals (+ size n) depth fuel))
              (6 7)
              (let [^objects args (.-args ^Node c)]
                (if (and (= 7 (.-op ^Node c)) (zero? (alength args)))
                  (recur 1 (primitive! (.-value ^Node c) (ArrayList.)) locals size depth fuel)
                  (do (push-frame! frames depth 2 c locals size)
                      (recur 0 (if (= 6 (.-op ^Node c)) (.-a ^Node c) (aget args 0))
                             locals size (inc depth) fuel)))))
            (let [depth (dec depth) ^objects frame (.get frames (int depth))
                  tag (long (aget frame 0)) node (aget frame 1)
                  ^objects saved (aget frame 2) saved-size (long (aget frame 3))]
              (case tag
                0 (let [saved (grow saved saved-size)]
                    (put! saved (int saved-size) c)
                    (recur 0 node saved (inc saved-size) depth fuel))
                1 (recur 0 (if c (.-b ^Node node) (.-c ^Node node)) saved saved-size depth fuel)
                2 (let [^ArrayList values (aget frame 4)
                        _ (.add values c)
                        next-index (long (aget frame 5))
                        app? (= 6 (.-op ^Node node))
                        ^objects args (.-args ^Node node)
                        next-index (if app? next-index (inc next-index))]
                    (if (< next-index (alength args))
                      (do (put! frame 5 (if app? (inc next-index) next-index))
                          (recur 0 (aget args next-index) saved saved-size (inc depth) fuel))
                      (if-not app?
                        (recur 1 (primitive! (.-value ^Node node) values) saved saved-size depth fuel)
                        (let [f (.get values 0)]
                          (when-not (instance? PrivateClosure f) (decline :call-target))
                          (let [^PrivateClosure f f ^Node term (.-term f) ^objects captured (.-captured f)
                                argc (dec (.size values)) n (alength captured)
                                _ (when-not (= argc (.-arity term)) (decline :arity))
                                ;; Sealed captures never alias working arrays.
                                ;; Reuse only if no active frame observes this one.
                                target (if-not (saved-array? frames depth saved) (grow saved (+ n argc))
                                           (object-array (max 16 (inc (+ n argc)))))]
                            (System/arraycopy captured 0 target 0 n)
                            (dotimes [i argc] (put! target (+ n i) (.get values (inc i))))
                            (recur 0 (.-a term) target (+ n argc) depth fuel))))))))))))))

(defn result [{:keys [registers]}] (aget ^objects registers 1))

(defn freeze
  "Copy active working state into an opaque, reusable in-memory snapshot.
   Closure captures are sealed immutable arrays; active locals/values are copied.
   This does not serialize continuations, authority or arbitrary host objects."
  [{:keys [registers frames]}]
  (let [^objects r registers depth (long (aget r 4))
        ^objects rcopy (aclone r)]
    (put! rcopy 2 (aclone ^objects (aget r 2)))
    (Frozen. rcopy
             (mapv (fn [i]
                     (let [^objects f (.get ^ArrayList frames i) copy (aclone f)]
                       (put! copy 2 (aclone ^objects (aget f 2)))
                       (put! copy 4 (.toArray ^ArrayList (aget f 4))) copy))
                   (range depth)))))

(defn thaw [^Frozen frozen]
  (let [^objects r (aclone ^objects (.-registers frozen)) frames (ArrayList.)]
    (put! r 2 (aclone ^objects (aget r 2)))
    (doseq [^objects f (.-frames frozen)]
      (let [copy (aclone f)]
        (put! copy 2 (aclone ^objects (aget f 2)))
        (put! copy 4 (ArrayList. (Arrays/asList ^objects (aget f 4))))
        (.add frames copy)))
    {:registers r :frames frames}))

(defn run! [machine]
  (while (= :paused (advance! machine 100000)))
  (result machine))

(defn prepare
  "Prepare a private entry. An optional caller-owned Map records each prepared
   node's exact source Core for reconstruction; this work is preparation-only."
  ([term] (prepare term nil))
  ([term origins]
   (core/assert-wf! term)
   (validate! term)
   (let [f (run! (machine (predecode term origins)))]
     (when-not (instance? PrivateClosure f) (decline :entry-function))
     f)))

(defn start [^PrivateClosure f args]
  (when-not (every? data? args) (decline :input))
  (let [^Node term (.-term f) ^objects captured (.-captured f) n (alength captured)]
    (when-not (= (.-arity term) (count args)) (decline :arity))
    (let [m (machine (.-a term)) ^objects r (:registers m)
          locals (object-array (max 16 (inc (+ n (count args)))))]
      (System/arraycopy captured 0 locals 0 n)
      (doseq [[i v] (map-indexed vector args)] (put! locals (+ n i) v))
      (put! r 2 locals) (put! r 3 (+ n (count args))) m)))

(defn invoke [f & args]
  (let [value (run! (start f args))]
    (when-not (data? value) (decline :output)) value))
