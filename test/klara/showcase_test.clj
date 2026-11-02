(ns klara.showcase-test
  "The showcase programs (design/PLAN.md#showcase-programs) run as tests."
  (:require [clojure.edn]
            [klara.host.precompile :as pre]
            [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(defn- run [path]
  (k/load-file (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)}) path))

(deftest interpreter-to-compiler   ; L4.jit.context L4.jit.attach L4.jit.function L4.check.speculate-value L4.jit.simplify L4.check.delta-data
  (let [r (run "showcases/interpreter_to_compiler.clj")]
    (testing "the user's specializer is checked and installed"
      (is (= [:ready :definitional 1] [(:status r) (:evidence r) (:speculations r)])))
    (testing "compiled and interpreted agree; another expression falls back to the interpreter"
      (is (:same-result r))
      (is (= 42 (:other-expression r))))
    (testing "it pays"
      (is (< 3 (:speedup r))))
    (testing "without the guard the generated code does not mean the interpreter"
      (is (= :rejected (:unguarded r))))
    (testing "a caller that passes a known definition needs no guard: the call is specialized away"
      (is (= :ready (:driver r)))
      (is (every? (set (:driver-premises r)) '[showcases.interpreter-to-compiler/calc
                                               showcases.interpreter-to-compiler/model]))
      (is (:same-specialized r)))))

(deftest speculate-fail-continue  ; L4.check.speculate-assume L4.jit.inline L4.exec.osr L4.exec.mint-safe L2.view.children
  (let [r (run "showcases/speculate_fail_continue.clj")]
    (testing "a loop that performs an effect compiles only by speculating on its cold branch"
      (is (= [:rejected :ready 1] [(:without-speculation r) (:status r) (:speculations r)])))
    (testing "the refund leaves compiled code once; the effect happens once; the result is the interpreter's"
      (is (= [true 1 :left] [(:same-result r) (:reviews r) (:left-at-refund r)])))
    (testing "after the effect the loop runs compiled again"
      (is (pos? (:reentered-compiled-loop r))))
    (testing "inlining made the helper a premise: changing it retires the compiled loop, not in the old world"
      (is (= :interpreted (:after-fee-change-runs r)))
      (is (:old-world-keeps r))
      (is (#{:compiled :left} (:old-world-path r))))))

(deftest precompiled   ; L4.profile.saved
  (let [file "showcases/precompiled.clj"
        dir (.getParent (.getAbsoluteFile (java.io.File. file)))
        first-run (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)})
        _ (k/load-file first-run file)
        saved (pre/saved-profiles first-run #(pre/program-namespace? first-run dir %))
        second-run (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)})
        outcomes (pre/install! second-run (clojure.edn/read-string (pr-str saved)))
        r (k/load-file second-run file)]
    (testing "the saved profile is small and names the program's functions, not the libraries'"
      (is (contains? saved 'showcases.precompiled/settle))
      (is (not-any? #(.startsWith (namespace %) "klara.") (keys saved)))
      (is (< (count (pr-str saved)) 4000)))
    (testing "the second run compiles settle before its first call, which runs compiled"
      (is (= :ready (get @outcomes 'showcases.precompiled/settle)))
      (is (#{:compiled :left} (:ran r)))
      (is (= 217801084 (:total r))))))

(deftest investor   ; L3.job.parallel L4.exec.provenance
  (let [r (run "showcases/investor.clj")]
    (testing "the investor compiles the loop and declines what does not pay"
      (is (= :compiled (get-in r [:decisions 'showcases.investor/rank])))
      (is (= :default (get-in r [:chosen 'showcases.investor/rank])))
      (is (= :not-hot (get-in r [:decisions 'showcases.investor/banner]))))
    (testing "decisions are kept in the world"
      (is (pos? (:recorded r))))
    (testing "the compiled loop records how it came about"
      (is (= :default (get-in r [:provenance :specializer])))
      (is (= :compiled (get-in r [:provenance :decision :decision])))
      (is (some #{'showcases.investor/rank} (map first (:premises r)))))
    (testing "same result, faster"
      (is (:same-result r))
      ;; a timing bound loose enough for a loaded machine (typically 35-60x)
      (is (< 2 (:speedup r))))))

(deftest in-place   ; L4.check.in-place
  (let [r (run "showcases/in_place.clj")]
    (testing "the investor owns the accumulator, the kernel admits it, nothing observable changes"
      (is (= [:in-place :in-place true] [(:chosen r) (:evidence r) (:same-result r)])))
    (testing "allocation drops by more than an order of magnitude"
      (is (< (* 10 (:bytes-after r)) (:bytes-before r))))
    (testing "an accumulator handed to another function is refused"
      (is (= :rejected (:refused r))))))

(deftest regex   ; L4.jit.rules L4.check.fix L2.code.recur L4.jit.attach
  (let [r (run "showcases/regex.clj")]
    (testing "the user rule's matcher is admitted against the interpreter, the sloppy one is not"
      (is (= :rejected (:sloppy r)))
      (is (= :compiled (get-in r [:decisions 'showcases.regex/matches?])))
      (is (#{:attached :default} (get-in r [:chosen 'showcases.regex/matches?]))))
    (testing "compiled and interpreted agree"
      (is (:same-result r))
      (is (:agree r)))
    (testing "faster (typically several hundred times)"
      (is (< 20 (:speedup r))))))

(deftest accounting   ; L3.account.holds L3.account.token L3.account.receipt L3.affine.reuse L3.job.parallel
  (let [r (run "showcases/accounting.clj")]
    (testing "three readers share three connections; each answer spent half a euro"
      (is (= 3 (count (:answers r))))
      (is (= {:eur 1/2} (:spent-per-answer r))))
    (testing "a fourth reader does not start"
      (is (= :L3.account.insufficient (:fourth-reader r))))
    (testing "reusing a consumed token fails its job, which is still charged"
      (is (= :L3.affine.reuse (:mistake r)))
      (is (= {:eur 33/4 :db 3} (:wallet r))))
    (testing "receipts balance and map to kontor transfers"
      (is (:balanced r))
      (is (= [:grant :consume :return] (mapv :kind (:kontor r))))
      (is (= 0.5M (get-in (:kontor r) [1 :resources "eur"]))))))

;; The independent state-machine baseline for showcases/smc.clj: particle
;; state as data, the same keys, draws and systematic resampling.
(defn- smc-plain []
  (let [M 2147483647
        next-key (fn [key] (mod (* 48271 key) M))
        split-key (fn [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
        uniform (fn [key] (/ (double key) M))
        emission (fn [p n] (loop [i n q 0.5] (if (> i 0) (recur (dec i) (/ (+ q p) 2.0)) q)))
        ys [true true false true false true false false true true true false]]
    (loop [ps (mapv (fn [i] (let [key (next-key (split-key 42 i))] {:x (< (uniform key) 0.5) :key key})) (range 32))
           obs ys key 42 z 1.0]
      (if (empty? obs)
        [(count (filter :x ps)) z]
        (let [weighted (mapv (fn [p] (let [q (emission (if (:x p) 0.9 0.2) 16)] (assoc p :w (if (first obs) q (- 1.0 q))))) ps)
              total (reduce + (map :w weighted))
              key2 (next-key key)
              kids (loop [j 0 i 0 acc (:w (first weighted)) out []]
                     (if (= j 32) out
                         (if (< acc (* (/ (+ (uniform key2) j) 32) total))
                           (recur j (inc i) (+ acc (:w (nth weighted (inc i)))) out)
                           (recur (inc j) i acc (conj out (nth weighted i))))))
              children (mapv (fn [i p] (let [split (split-key (:key p) i)
                                             draw (if (next obs) (next-key split) split)]
                                         {:key draw :x (if (next obs) (< (uniform draw) (if (:x p) 0.8 0.2)) (:x p))}))
                             (range 32) kids)]
          (recur children (next obs) key2 (* z (/ total 32))))))))

(deftest smc   ; L3.cont.multishot L3.handle.deep L4.lower.calls
  (let [r (run "showcases/smc.clj")]
    (is (= :ready (:kernel r)))
    (is (= :compiled (:kernel-path r)))
    (is (= (smc-plain) (:interpreted r) (:compiled r)))))
