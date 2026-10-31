(ns certified-identity
  "A proof-carrying candidate (L4.check.certificate): (* x 1) is not x
  definitionally (it throws for non-numbers), but for 64-bit integers it is.
  The certificate proves that about the actual terms; the executable checks
  that its argument is a long and otherwise runs the reference."
  (:require [klara.stage :refer [code]]
            [klara.compiler :as compiler]))

(def reference (code (fn [x] (* x 1))))
(def candidate (fn [_] (code (fn [x] x))))

;; The proof, in ansatz tactics. %ref and %cand are the two configurations
;; the certifier states the theorem about.
(def proof
  '[(have hr (= PrimRes (primApply PrimOp.mul (Datum.int i) (Datum.int (Int.ofNat 1))) (PrimRes.ok (Datum.int i))))
    (simp only [primApply, intOp])
    (have hm (= Int (* i (Int.ofNat 1)) i)) (exact (Int.mul_one i))
    (rw [hm]) (exact (checked-in-range i hi))
    (apply (equiv-of-reach %ref %cand (Config.mk World.empty Worlds.none 0 (Tm.lit (Datum.int i)))))
    (exact (reach-beta %world %worlds 0 %ref-body %arg
                       (Tm.prim PrimOp.mul (Tm.lit (Datum.int i)) (Tm.lit (Datum.int (Int.ofNat 1))))
                       (Config.mk %world %worlds 0 %arg) (rfl) (rfl)
             (reach-prim %world %worlds 0 PrimOp.mul (Datum.int i) (Datum.int (Int.ofNat 1)) (Datum.int i)
                         (Config.mk %world %worlds 0 %arg) hr (Star.refl (Config.mk %world %worlds 0 %arg)))))
    (exact (reach-beta %world %worlds 0 %cand-body %arg %arg (Config.mk %world %worlds 0 %arg) (rfl) (rfl)
                       (Star.refl (Config.mk %world %worlds 0 %arg))))])

(def without (compiler/prepare reference {:recipe candidate}))
(def with-proof (compiler/prepare reference {:recipe candidate :certificate {:kind :ansatz :proof proof}}))
(def wrong-proof (compiler/prepare reference {:recipe candidate :certificate {:kind :ansatz :proof '[(rfl)]}}))

(def f (compiler/executable with-proof))

[(:status without) (:rule without)
 (:status with-proof) (:guards (compiler/explain f))
 (f 41) (:last-path (compiler/explain f))
 (try (f "a") (catch ClassCastException e :reference-semantics)) (:last-path (compiler/explain f))
 (:status wrong-proof) (:rule wrong-proof)]
