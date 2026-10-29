;; Narrow Java-source backend probe. Accept exactly the S20 f -> g loop IR;
;; fail closed for every other program. Source emission lets javap inspect the
;; intended primitive ABI before a general K3 bytecode backend exists.
(require '[klara.world :as w] '[klara.defs :as d]
         '[klara.compile.core :as cc] '[clojure.java.io :as io])

(defn expect! [ok description]
  (when-not ok (throw (ex-info (str "typed probe: " description) {}))))

(defn checked-shape [g f]
  (let [gir (:ir g) fir (:ir f)
        x (first (:params gir)) n (first (:params fir))
        factor (get-in gir [:body :args 1 :datum])
        l (get-in fir [:body :inits 0])
        [i s] (:params l)
        test (get-in l [:body :body :test])
        then (get-in l [:body :body :then])
        gcall (get-in then [:args 1 :args 1])
        entry (get-in fir [:body :body])]
    (expect! (= {:op :fn :arity 1 :rest? false}
                (select-keys gir [:op :arity :rest?])) "g arity")
    (expect! (= {:op :prim :name '* :args [{:op :local :name x}
                                         {:op :quote :datum factor}]}
                (:body gir)) "g body")
    (expect! (and (instance? Long factor) (pos? factor)) "long factor")
    (expect! (= {:args [:long] :return :long} (:return-layout g))
             "proved long return")
    (expect! (and (= :fn (:op fir)) (= 1 (:arity fir))
                  (= :letrec (get-in fir [:body :op]))
                  (= 1 (count (get-in fir [:body :inits])))
                  (= :fn (:op l)) (= 2 (:arity l))
                  (= :loop-check (get-in l [:body :op]))) "loop header")
    (expect! (= {:op :prim :name '>
                 :args [{:op :local :name i} {:op :quote :datum 0}]}
                test) "loop condition")
    (expect! (= {:op :local :name s} (get-in l [:body :body :else]))
             "loop result")
    (expect! (= {:op :app :fn {:op :local :name (first (get-in fir [:body :names]))}
                 :args [{:op :prim :name 'dec :args [{:op :local :name i}]}
                        {:op :prim :name '+
                         :args [{:op :local :name s} gcall]}]}
                then) "loop recurrence")
    (expect! (= {:op :app :fn {:op :local :name (first (get-in fir [:body :names]))}
                 :args [{:op :local :name n} {:op :quote :datum 0}]}
                entry) "loop entry")
    (expect! (= {:op :app :fn {:op :resolve :id 'g}
                 :args [{:op :local :name i}]}
                gcall) "residual g call")
    (let [world-guard (first (filter #(and (= :world (first %)) (= 'g (second %)))
                                     (:guards f)))]
      (expect! world-guard "pinned g value-id guard")
      {:factor factor :value-id (nth world-guard 2)})))

(defn java-source [class-name {:keys [factor value-id]}]
  (format (str "package klara.typedprobe;\n"
               "public final class %s {\n"
               "  public static final String G_VALUE_ID = \"%s\";\n"
               "  private %s() {}\n"
               "  public static long g(long x) { return Math.multiplyExact(x, %dL); }\n"
               "  public static long run(Context c, long n) {\n"
               "    if (!G_VALUE_ID.equals(c.gValueId())) throw new IllegalStateException(\"guard failed\");\n"
               "    long i = n, s = 0L;\n"
               "    while (i > 0L) {\n"
               "      long nextI = Math.decrementExact(i);\n"
               "      long nextS = Math.addExact(s, g(i));\n"
               "      i = nextI; s = nextS;\n"
               "    }\n"
               "    return s;\n"
               "  }\n"
               "}\n")
          class-name value-id class-name factor))

(let [out (io/file (or (first *command-line-args*)
                       "experiments/typed_jit/generated"))]
  (.mkdirs out)
  (doseq [[class-name factor] [["F2" 2] ["F3" 3]]]
    (let [world (w/make-world)
          _ (d/define! world (list 'def 'g (list 'fn '[x] (list '* 'x factor))))
          _ (d/define! world '(def f (fn [n]
                                      (loop [i n s 0]
                                        (if (> i 0)
                                          (recur (dec i) (+ s (g i))) s)))))
          opts {:inline-fuel 0}
          g (cc/compile-def world 'g opts)
          f (cc/compile-def world 'f opts)
          shape (checked-shape g f)]
      (spit (io/file out (str class-name ".java"))
            (java-source class-name shape))
      (println {:class class-name :code-id (:code-id f)
                :g-value-id (:value-id shape)
                :return-layout (:return-layout g)
                :frame-states (count (:frame-states f))}))))
