(ns awfy.mandelbrot
  "Are We Fast Yet? Mandelbrot (Marr et al., DLS 2016): double arithmetic
  in nested loops, results folded into bits. Plain Clojure: the same file
  runs on Clojure and on Klara.")

(defn mandelbrot [size]
  (loop [y 0 sum 0 byte-acc 0 bit-num 0]
    (if (< y size)
      (let [ci (- (/ (* 2.0 y) size) 1.0)
            [sum byte-acc bit-num]
            (loop [x 0 sum sum byte-acc byte-acc bit-num bit-num]
              (if (< x size)
                (let [cr (- (/ (* 2.0 x) size) 1.5)
                      escape (loop [z 0 zrzr 0.0 zi 0.0 zizi 0.0]
                               (if (< z 50)
                                 (let [zr (+ (- zrzr zizi) cr)
                                       zi (+ (* 2.0 zr zi) ci)
                                       zrzr (* zr zr)
                                       zizi (* zi zi)]
                                   (if (> (+ zrzr zizi) 4.0) 1 (recur (inc z) zrzr zi zizi)))
                                 0))
                      byte-acc (+ (bit-shift-left byte-acc 1) escape)
                      bit-num (inc bit-num)]
                  (cond (= bit-num 8) (recur (inc x) (bit-xor sum byte-acc) 0 0)
                        (= x (dec size)) (recur (inc x) (bit-xor sum (bit-shift-left byte-acc (- 8 bit-num))) 0 0)
                        :else (recur (inc x) sum byte-acc bit-num)))
                [sum byte-acc bit-num]))]
        (recur (inc y) sum byte-acc bit-num))
      sum)))

(defn run [] (mandelbrot 500))
(def expected 191)
