(ns klara.formal.gen
  "Random Klara programs inside the formal fragment, for differential
  testing of the CEK machine against the kernel-checked semantics.

  Programs are ordinary Klara source (they go through the reader and the
  expander). Generation is seeded and reproducible. Expressions are mostly
  well-behaved (integer arithmetic on small numbers) with a controlled share
  of type errors, overflows, unhandled effects and staging errors, so both
  normal results and every kind of stuck state are compared."
  (:import [java.util Random]))

(defn- pick [^Random r xs] (nth xs (.nextInt r (count xs))))
(defn- chance [^Random r p] (< (.nextDouble r) p))

(def ops [:ask :tell :flip])

(defn- int-leaf [^Random r]
  (if (chance r 0.03)
    (pick r [Long/MAX_VALUE Long/MIN_VALUE 4611686018427387904])
    (- (.nextInt r 21) 10)))

(declare expr)

(defn- leaf [^Random r {:keys [locals]}]
  (let [ls (vec locals)]
    (cond
      (and (seq ls) (chance r 0.45)) (pick r ls)
      (chance r 0.8) (int-leaf r)
      :else (pick r [true false nil :a :b]))))

(defn- fresh [ctx base] (symbol (str base (count (:locals ctx)) "_" (:depth ctx 0))))

(defn- bind [ctx x] (update ctx :locals (fnil conj []) x))

(defn- code-expr
  "A stage-1 expression inside (code ...): future-stage locals in
   :code-locals, present-stage locals are lifted implicitly."
  [^Random r ctx d]
  (let [cl (vec (:code-locals ctx))]
    (if (or (zero? d) (chance r 0.3))
      (cond (and (seq cl) (chance r 0.5)) (pick r cl)
            :else (leaf r (assoc ctx :locals (:locals ctx))))
      (case (.nextInt r 5)
        0 (list (pick r '[+ - *]) (code-expr r ctx (dec d)) (code-expr r ctx (dec d)))
        1 (list 'esc (cond (chance r 0.05) (int-leaf r)             ; L2.esc.not-code
                           (chance r 0.5) (list 'lift (expr r ctx (dec d)))
                           :else (list 'code (code-expr r ctx (dec d)))))
        2 (let [x (fresh ctx "c")]
            (list 'let [x (code-expr r ctx (dec d))]
                  (code-expr r (update ctx :code-locals (fnil conj []) x) (dec d))))
        3 (list 'if (code-expr r ctx (dec d)) (code-expr r ctx (dec d)) (code-expr r ctx (dec d)))
        4 (if (seq cl)
            (list 'esc (list 'code (pick r cl)))
            (code-expr r ctx (dec d)))))))

(defn expr [^Random r ctx d]
  (let [ctx (update ctx :depth (fnil inc 0))]
    (if (or (zero? d) (chance r 0.15))
      (leaf r ctx)
      (case (.nextInt r 14)
        0 (list (pick r '[+ - * + -]) (expr r ctx (dec d)) (expr r ctx (dec d)))
        1 (list (pick r '[= < > <= >=]) (expr r ctx (dec d)) (expr r ctx (dec d)))
        2 (list (pick r '[inc dec zero? not]) (expr r ctx (dec d)))
        3 (list 'if (expr r ctx (dec d)) (expr r ctx (dec d)) (expr r ctx (dec d)))
        4 (let [x (fresh ctx "x")]
            (list 'let [x (expr r ctx (dec d))] (expr r (bind ctx x) (dec d))))
        5 (let [x (fresh ctx "p")]
            (list (list 'fn [x] (expr r (bind ctx x) (dec d))) (expr r ctx (dec d))))
        6 (let [x (fresh ctx "p") y (fresh ctx "q")]
            (list (list 'fn [x y] (expr r (bind (bind ctx x) y) (dec d)))
                  (expr r ctx (dec d)) (expr r ctx (dec d))))
        7 (cond (chance r 0.1) (list (leaf r ctx) (expr r ctx (dec d)))   ; apply a non-function
                (seq (:fns ctx)) (list (pick r (vec (:fns ctx))) (expr r ctx (dec d)))
                :else (leaf r ctx))
        8 (list 'perform (pick r ops) (expr r ctx (dec d)))
        9 (let [op (pick r ops) k (fresh ctx "k") v (fresh ctx "v")
                  clause (case (.nextInt r 4)
                           0 (list 'fn [k v] (list k (expr r (bind ctx v) (dec d))))
                           1 (list 'fn [k v] (list '+ (list k v) (list k (expr r (bind ctx v) (dec d)))))
                           2 (list 'fn [k v] (expr r (bind ctx v) (dec d)))
                           3 (list 'fn [k v] (list k (list k v))))]
              (list 'handle (cond-> {op clause}
                              (chance r 0.3) (assoc :return (let [y (fresh ctx "y")]
                                                              (list 'fn [y] (expr r (bind ctx y) (dec d))))))
                    (expr r ctx (dec d))))
        10 (list 'run (list 'code (code-expr r ctx (dec d))))
        11 (let [x (fresh ctx "z")]
             (list (list 'run (list 'code (list 'fn [x] (code-expr r (update ctx :code-locals (fnil conj []) x) (dec d)))))
                   (expr r ctx (dec d))))
        12 (list 'run (list 'lift (expr r ctx (dec d))))
        13 (let [n (fresh ctx "n")]
             (list 'loop [n (list 'mod* (expr r ctx (dec d)))]
                   (list 'if (list '< n 1) (expr r (bind ctx n) (dec d)) (list 'recur (list 'dec n)))))))))

(defn program
  "A program as Klara source text: a few definitions, then expressions."
  [seed]
  (let [r (Random. seed)
        defs (vec (for [i (range (.nextInt r 3))]
                    (let [f (symbol (str "f" i)) x (symbol (str "a" i))]
                      [f (list 'defn f [x] (expr r {:locals [x]} 3))])))
        fns (map first defs)
        exprs (for [_ (range (inc (.nextInt r 3)))]
                (expr r {:fns fns} 4))]
    (str "(ns gen (:require [klara.stage :refer [code esc lift run]] [klara.effect :refer [perform handle]]))\n"
         ;; a bounded counter for loops, so generated loops terminate
         "(defn mod* [n] (if (< n 0) 0 (if (< 5 n) 5 n)))\n"
         (apply str (map #(str (pr-str (second %)) "\n") defs))
         (apply str (map #(str (pr-str %) "\n") exprs)))))
