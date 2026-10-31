(ns interpreter.activation
  "Experimental boxed activation programs sharing private closure values and
   the bridge controller with the node interpreter. No production registration."
  (:refer-clojure :exclude [prepare])
  (:require [interpreter.bridge :as bridge] [interpreter.mutable :as m]
            [klara.core :as core])
  (:import [interpreter.mutable Node PrivateClosure]
           [java.util ArrayList Arrays IdentityHashMap Collections Map]))

(deftype Instruction [^long op ^long a ^long b ^long c ^long d ^long lex extra])
(deftype Program [node ^long captures ^long arity ^long locals ^long temps ^objects code ^objects points])
(deftype FrozenActivation [state])

(defn- put! [^objects a ^long i v] (aset a (int i) v))
(defn- decline! [reason] (throw (ex-info "activation: declined" {:activation/decline reason})))

(defn- compile-program! [^IdentityHashMap plans ^Node function captures]
  (or (.get plans function)
      (let [code (ArrayList.) points (ArrayList.) next-temp (atom 0)
            max-local (atom (+ captures (.-arity function)))]
        (letfn [(temps! [n] (let [i @next-temp] (swap! next-temp + n) (- -1 i)))
                (emit! [op a b c d lex extra point]
                  (let [pc (.size code)]
                    (.add code (Instruction. op a b c d lex extra)) (.add points point) pc))
                (patch! [pc op a b c d lex extra]
                  (.set code pc (Instruction. op a b c d lex extra)))
                (expr! [^Node node size dest frames tail?]
                  (swap! max-local max size (if (neg? dest) 0 (inc dest)))
                  (let [point {:mode :eval :node node :size size :frames frames}]
                    (case (.-op node)
                      0 (emit! 0 dest 0 0 0 size (.-value node) point)
                      1 (emit! 1 dest (- size 1 (.-index node)) 0 0 size nil point)
                      2 (do (compile-program! plans node size)
                            (emit! 2 dest size 0 0 size node point))
                      3 (do (expr! (.-a node) size size
                                   (conj frames {:tag 0 :node (.-b node) :size size}) false)
                            (expr! (.-b node) (inc size) dest frames tail?))
                      4 (let [test (temps! 1)]
                          (expr! (.-a node) size test
                                 (conj frames {:tag 1 :node node :size size}) false)
                          (let [branch (emit! 6 test 0 0 0 size node nil)
                                then-pc (.size code)]
                            (expr! (.-b node) size dest frames tail?)
                            (let [jump (emit! 7 0 0 0 0 size nil nil) else-pc (.size code)]
                              (expr! (.-c node) size dest frames tail?)
                              (patch! branch 6 test then-pc else-pc 0 size node)
                              (patch! jump 7 (.size code) 0 0 0 size nil))))
                      5 (let [^objects inits (.-args node) n (alength inits)]
                          (dotimes [i n] (compile-program! plans (aget inits i) (+ size n)))
                          (emit! 3 size n 0 0 size node point)
                          (expr! (.-a node) (+ size n) dest frames tail?))
                      (6 7)
                      (let [app? (= 6 (.-op node)) ^objects args (.-args node)
                            n (+ (alength args) (if app? 1 0)) window (temps! n)
                            operands (if app? (cons (.-a node) (seq args)) (seq args))]
                        (doseq [[i operand] (map-indexed vector operands)]
                          (expr! operand size (- window i)
                                 (conj frames {:tag 2 :node node :size size
                                               :vals (mapv #(- window %) (range i))}) false))
                        (emit! (if app? 5 4) dest window (alength args) (if tail? 1 0) size node
                               {:mode :finish :node node :size size :frames frames
                                :vals (mapv #(- window %) (range n))})))))]
          (let [result (temps! 1)]
            (expr! (.-a function) (+ captures (.-arity function)) result [] true)
            (emit! 8 result 0 0 0 0 nil {:mode :ret :result result :frames []})
            (let [locals @max-local reg #(if (neg? %) (+ locals (dec (- %))) %)
                  relocated
                  (mapv (fn [^Instruction i]
                          (let [op (.-op i) a (.-a i) b (.-b i)]
                            (Instruction. op
                              (if (#{0 1 2 4 5 6 8} op) (reg a) a)
                              (if (#{4 5} op) (reg b) b)
                              (.-c i) (.-d i) (.-lex i) (.-extra i)))) code)
                  relocate-frame #(cond-> % (:vals %) (update :vals (fn [xs] (mapv reg xs))))
                  points (mapv #(when % (cond-> (update % :frames (fn [fs] (mapv relocate-frame fs)))
                                          (:vals %) (update :vals (fn [xs] (mapv reg xs)))
                                          (:result %) (update :result reg))) points)
                  program (Program. function captures (.-arity function) locals @next-temp
                                    (object-array relocated) (object-array points))]
              (.put plans function program)
              program))))))

(defn- invoke-primitive! [name ^objects slots ^long start ^long n]
  (let [f (get (m/primitive-roots) name)]
    (when-not (identical? f (get core/prims name)) (decline! :primitive-context))
    (dotimes [i n]
      (when-not (m/primitive-data? (aget slots (+ start i))) (decline! :primitive-operands)))
    (case n
      0 (f) 1 (f (aget slots start)) 2 (f (aget slots start) (aget slots (inc start)))
      3 (f (aget slots start) (aget slots (inc start)) (aget slots (+ start 2)))
      4 (f (aget slots start) (aget slots (inc start)) (aget slots (+ start 2)) (aget slots (+ start 3)))
      5 (f (aget slots start) (aget slots (inc start)) (aget slots (+ start 2)) (aget slots (+ start 3)) (aget slots (+ start 4)))
      (apply f (mapv #(aget slots (+ start %)) (range n))))))

(defn- find-program ^Program [^Map plans ^PrivateClosure f n]
  (let [^Program p (.get plans (.-term f))]
    (when-not (and p (= n (.-arity p)) (= (alength ^objects (.-captured f)) (.-captures p)))
      (decline! :call-layout)) p))

(defn start [plans ^PrivateClosure f args]
  (when-not (every? m/data? args) (decline! :input))
  (let [p (find-program plans f (count args)) slots (object-array (+ (.-locals p) (.-temps p)))
        ^objects captured (.-captured f) n (alength captured)]
    (System/arraycopy captured 0 slots 0 n)
    (doseq [[i v] (map-indexed vector args)] (put! slots (+ n i) v))
    {:plans plans :frames (ArrayList.) :scratch (object-array [(object-array 8)])
     :registers (object-array [p slots 0 (+ n (count args)) 0 false nil])}))

(defn advance! [{:keys [plans frames registers scratch]} fuel]
  (when-not (and (integer? fuel) (<= 0 fuel Long/MAX_VALUE)) (decline! :fuel))
  (let [^Map plans plans ^ArrayList frames frames ^objects r registers ^objects scratch scratch]
    (loop [program (aget r 0) slots (aget r 1) pc (long (aget r 2))
           last-size (long (aget r 3)) depth (long (aget r 4)) fuel (long fuel)]
      (if (or (zero? fuel) (true? (aget r 5)))
        (do (put! r 0 program) (put! r 1 slots) (put! r 2 pc)
            (put! r 3 last-size) (put! r 4 depth)
            (if (true? (aget r 5)) :done :paused))
        (let [^Program p program ^objects slots slots ^Instruction i (aget ^objects (.-code p) pc)
              op (.-op i) a (.-a i) b (.-b i) c (.-c i) lex (.-lex i) fuel (dec fuel)]
          (case op
            0 (do (put! slots a (.-extra i)) (recur p slots (inc pc) lex depth fuel))
            1 (do (put! slots a (aget slots b)) (recur p slots (inc pc) lex depth fuel))
            2 (do (put! slots a (PrivateClosure. (.-extra i) (Arrays/copyOf slots (int b))))
                  (recur p slots (inc pc) lex depth fuel))
            3 (let [^Node node (.-extra i) ^objects inits (.-args node)
                    captured (Arrays/copyOf slots (int (+ a b)))]
                (dotimes [j b]
                  (let [f (PrivateClosure. (aget inits j) captured)]
                    (put! captured (+ a j) f) (put! slots (+ a j) f)))
                (recur p slots (inc pc) (+ a b) depth fuel))
            4 (do (put! slots a (invoke-primitive! (.-value ^Node (.-extra i)) slots b c))
                  (recur p slots (inc pc) lex depth fuel))
            5 (let [f (aget slots b)]
                (when-not (instance? PrivateClosure f) (decline! :call-target))
                (let [^PrivateClosure f f target (find-program plans f c)
                      ^objects captured (.-captured f) n (alength captured)
                      tail? (= 1 (.-d i)) required (+ (.-locals target) (.-temps target))
                      reuse? (and tail? (>= (alength slots) required))
                      target-slots (if reuse? slots (object-array required))]
                  (when-not tail?
                    (let [^objects frame (if (< depth (.size frames)) (.get frames (int depth))
                                            (let [f (object-array 5)] (.add frames f) f))]
                      (put! frame 0 p) (put! frame 1 slots) (put! frame 2 (inc pc))
                      (put! frame 3 a) (put! frame 4 pc)))
                  (if reuse?
                    (let [^objects old (aget scratch 0)
                          ^objects buffer (if (>= (alength old) c) old
                                           (let [new (object-array c)] (put! scratch 0 new) new))]
                      (System/arraycopy slots (int (inc b)) buffer 0 (int c))
                      (Arrays/fill slots nil)
                      (System/arraycopy captured 0 target-slots 0 n)
                      (System/arraycopy buffer 0 target-slots n (int c))
                      (Arrays/fill buffer nil))
                    (do (System/arraycopy captured 0 target-slots 0 n)
                        (System/arraycopy slots (int (inc b)) target-slots n (int c))))
                  (recur target target-slots 0 (+ n c) (if tail? depth (inc depth)) fuel)))
            6 (recur p slots (if (aget slots a) b c) last-size depth fuel)
            7 (recur p slots a last-size depth fuel)
            8 (let [v (aget slots a)]
                (if (zero? depth)
                  (do (put! r 5 true) (put! r 6 v)
                      (recur p slots pc last-size depth fuel))
                  (let [depth (dec depth) ^objects frame (.get frames (int depth))
                        ^objects caller (aget frame 1)]
                    (put! caller (long (aget frame 3)) v)
                    (recur (aget frame 0) caller (long (aget frame 2)) last-size depth fuel))))))))))

(defn freeze [{:keys [registers frames plans]}]
  (let [^objects r registers copy (aclone r) ^ArrayList frames frames depth (long (aget r 4))]
    (put! copy 1 (aclone ^objects (aget r 1)))
    (FrozenActivation.
      {:plans plans :registers copy
       :frames (mapv (fn [j] (let [^objects f (.get frames j) copy (aclone f)]
                              (put! copy 1 (aclone ^objects (aget f 1))) copy)) (range depth))})))

(defn thaw [^FrozenActivation frozen]
  (let [{:keys [plans registers frames]} (.-state frozen) r (aclone ^objects registers)
        stack (ArrayList.)]
    (put! r 1 (aclone ^objects (aget r 1)))
    (doseq [^objects f frames]
      (let [copy (aclone f)] (put! copy 1 (aclone ^objects (aget f 1))) (.add stack copy)))
    {:plans plans :registers r :frames stack :scratch (object-array [(object-array 8)])}))

(defn result [{:keys [registers]}] (aget ^objects registers 6))

(defn project [{:keys [registers frames]}]
  (let [^objects r registers ^Program p (aget r 0) ^objects slots (aget r 1)
        depth (long (aget r 4)) last-size (long (aget r 3)) synthetic (ArrayList.)
        point (loop [pc (long (aget r 2))]
                (let [^Instruction i (aget ^objects (.-code p) pc)]
                  (case (.-op i)
                    6 (recur (if (aget slots (.-a i)) (.-b i) (.-c i)))
                    7 (recur (.-a i))
                    (aget ^objects (.-points p) pc))))
        append! (fn [point ^objects source]
                  (doseq [{:keys [tag node size vals]} (:frames point)]
                    (.add synthetic (object-array [tag node source size
                                                    (mapv #(aget source %) vals) 0]))))]
    (dotimes [j depth]
      (let [^objects f (.get ^ArrayList frames j) ^Program caller (aget f 0)]
        (append! (aget ^objects (.-points caller) (long (aget f 4))) (aget f 1))))
    (append! point slots)
    (let [{:keys [mode node size vals result]} point
          size (if (= mode :ret) last-size size)
          control (if (= mode :ret) (aget slots result) node)
          mode (case mode :eval 0 :ret 1 :finish 2)]
      {:registers (object-array [mode control slots size (.size synthetic) false
                                 (mapv #(aget slots %) vals)]) :frames synthetic})))

(defn prepare
  ([term] (prepare term {}))
  ([term options]
   (let [base (bridge/prepare term options) plans (IdentityHashMap.) seen (IdentityHashMap.)]
     (letfn [(walk [^PrivateClosure f]
               (when-not (.containsKey seen f)
                 (.put seen f true)
                 (compile-program! plans (.-term f) (alength ^objects (.-captured f)))
                 (doseq [v (.-captured f)] (when (instance? PrivateClosure v) (walk v)))))]
       (walk (:entry base)))
     (let [plans (Collections/unmodifiableMap plans)]
       (assoc base :programs plans :engine {:name :activation :start #(start plans %1 %2)
                                          :advance! advance! :freeze freeze :thaw thaw :project project
                                          :result result})))))
