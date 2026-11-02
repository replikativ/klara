(ns certified-horner
  "Proofs where they pay (design/PLAN.md, showcase 3): Horner's rule as a
  proof-carrying candidate under a range guard (L4.check.certificate).

  a*x*x + b*x + c and (a*x + b)*x + c are equal as integers, but not as
  Klara functions: with checked 64-bit arithmetic one may overflow where the
  other does not. For |x| <= 2^20 neither does, and the certificate proves
  the two functions equivalent there. The proof is computed by a Klara
  function from the coefficients and checked by the ansatz kernel against
  the actual quoted terms: one beta step and a chain of arithmetic steps on
  each side, every intermediate bounded by nlinarith from the range, and
  the two values equated by ring. The range becomes the runtime guard;
  outside it the executable runs the reference."
  (:require [klara.stage :refer [code esc lift]]
            [klara.compiler :as compiler]))

(defn poly [a b c] (code (fn [x] (+ (+ (* (esc (lift a)) (* x x)) (* (esc (lift b)) x)) (esc (lift c))))))
(defn horner [a b c] (code (fn [x] (+ (* (+ (* (esc (lift a)) x) (esc (lift b))) x) (esc (lift c))))))

;; ---------------------------------------------------------------------------
;; The certificate, as data: ansatz tactics over the formal Tm, where %ref,
;; %cand, %ref-body, %cand-body, %arg, %world and %worlds are the
;; certifier's names for the quoted terms (klara.formal.certify).

(defn- n [k] (list 'Int.ofNat k))
(defn- int-term [k] (if (neg? k) (list 'Int.negSucc (- (- k) 1)) (list 'Int.ofNat k)))
(defn- lit [v] (list 'Tm.lit (list 'Datum.int v)))
(defn- prim [op x y] (list 'Tm.prim (symbol (str "PrimOp." op)) x y))
(defn- ok [op] (if (= op "mul") 'prim-mul-ok 'prim-add-ok))

;; one arithmetic step x op y = v inside a context: (ev-prim-lit ...) wrapped
;; in the left/right frames of the path to it
(defn- step-at [path op x y v range-fact]
  (reduce (fn [inner [side op2 d]]
            (if (= side :l)
              (list 'ev-prim-l '%world '%worlds 0 0 (symbol (str "PrimOp." op2)) '_ '_ '_ inner)
              (list 'ev-prim-r '%world '%worlds 0 0 (symbol (str "PrimOp." op2)) (list 'Datum.int d) '_ '_ inner)))
          (list 'ev-prim-lit '%world '%worlds 0 (symbol (str "PrimOp." op)) (list 'Datum.int x) (list 'Datum.int y)
                (list 'Datum.int v) (list (ok op) x y range-fact))
          (reverse path)))

(defn- chain [steps final]
  (reduce (fn [acc s] (list 'reach-ev '%world '%worlds 0 '_ '_ '_ s acc)) final (reverse steps)))

(defn- in-range [fact v] [(list 'have fact (list '= 'Bool (list 'inRange v) 'Bool.true)) '(apply in-range) '(nlinarith) '(nlinarith)])

(defn horner-proof
  "The certificate that (poly a b c) = (horner a b c) for lo <= x <= hi."
  [a b c lo hi]
  (let [i 'i
        I (lit i)
        ii (list '* i i) a2 (list '* (n a) ii) a3 (list '* (n b) i) a4 (list '+ a2 a3) a5 (list '+ a4 (n c))
        c1 (list '* (n a) i) c2 (list '+ c1 (n b)) c3 (list '* c2 i) c4 (list '+ c3 (n c))
        r0 (prim "add" (prim "add" (prim "mul" (lit (n a)) (prim "mul" I I)) (prim "mul" (lit (n b)) I)) (lit (n c)))
        k0 (prim "add" (prim "mul" (prim "add" (prim "mul" (lit (n a)) I) (lit (n b))) I) (lit (n c)))
        ref-steps [(step-at [[:l "add"] [:l "add"] [:r "mul" (n a)]] "mul" i i ii 'r1)
                   (step-at [[:l "add"] [:l "add"]] "mul" (n a) ii a2 'r2)
                   (step-at [[:l "add"] [:r "add" a2]] "mul" (n b) i a3 'r3)
                   (step-at [[:l "add"]] "add" a2 a3 a4 'r4)
                   (step-at [] "add" a4 (n c) a5 'r5)]
        cand-steps [(step-at [[:l "add"] [:l "mul"] [:l "add"]] "mul" (n a) i c1 'q1)
                    (step-at [[:l "add"] [:l "mul"]] "add" c1 (n b) c2 'q2)
                    (step-at [[:l "add"]] "mul" c2 i c3 'q3)
                    (step-at [] "add" c3 (n c) c4 'q4)]
        end (list 'Config.mk '%world '%worlds 0 (lit c4))]
    (vec (concat
          [(list 'have 'b1 (list '<= (int-term lo) 'i)) '(exact (And.left hb))
           (list 'have 'b2 (list '<= 'i (int-term hi))) '(exact (And.right hb))]
          (mapcat in-range ['r1 'r2 'r3 'r4 'r5 'q1 'q2 'q3 'q4] [ii a2 a3 a4 a5 c1 c2 c3 c4])
          [(list 'have 'e (list '= 'Int a5 c4)) '(ring)
           (list 'apply (list 'equiv-of-reach '%ref '%cand end))
           '(rw [(Eq.symm e)])
           (list 'exact (list 'reach-beta '%world '%worlds 0 '%ref-body '%arg r0 '_ '(Eq.refl _) '(Eq.refl _)
                              (chain ref-steps (list 'Star.refl (list 'Config.mk '%world '%worlds 0 (lit a5))))))
           (list 'exact (list 'reach-beta '%world '%worlds 0 '%cand-body '%arg k0 '_ '(Eq.refl _) '(Eq.refl _)
                              (chain cand-steps (list 'Star.refl end))))]))))

;; ---------------------------------------------------------------------------
;; The showcase

(def bound 1048576)                     ; 2^20
(def reference (poly 3 5 7))
(defn recipe [_] (horner 3 5 7))

;; definitionally they differ (overflow behaviour), so the checker refuses
(def without (compiler/prepare reference {:recipe recipe}))
;; with the certificate and its range, the kernel admits it
(def with-proof (compiler/prepare reference {:recipe recipe
                                             :certificate {:kind :ansatz :range [(- bound) bound]
                                                           :proof (horner-proof 3 5 7 (- bound) bound)}}))
;; a range the bounds do not cover (|x| <= 2^40: x*x may reach 2^80) fails to check
(def too-wide (compiler/prepare reference {:recipe recipe
                                           :certificate {:kind :ansatz :range [(- 1099511627776) 1099511627776]
                                                         :proof (horner-proof 3 5 7 (- 1099511627776) 1099511627776)}}))

(def f (compiler/executable with-proof))

[(:status without) (:rule without)
 (:status with-proof) (:guards (compiler/explain f))
 (f 1000) (:last-path (compiler/explain f))
 ;; outside the range: the reference runs, and overflows as it does
 (try (f 3037000500) (catch ArithmeticException e :overflow)) (:last-path (compiler/explain f))
 (:status too-wide) (:rule too-wide)]
