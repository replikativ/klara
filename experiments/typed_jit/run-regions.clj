;; Load into a persistent Clojure REPL at the repository root.
(load-file "experiments/typed_jit/regions.clj")
(require '[klara.typed-regions :as regions] '[klara.world :as w]
         '[klara.defs :as d] '[klara.compile.core :as cc] '[klara.stage :as stage]
         '[clojure.java.io :as io])

(def region-programs
  [['(fn [x] (* x 2))
    '(fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s (g i))) s)))]
   ['(fn [x] (* x 3))
    '(fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s (g i))) s)))]
   ['(fn [x] (let [y (+ x 1)] (if (> y 4) (* y y) (- y 2))))
    '(fn [n] (loop [i n s 7] (if (> i 0)
                             (let [v (g i)] (recur (dec i) (+ s v))) s)))]
   ['(fn [x] (- x 5))
    '(fn [n] (loop [i n s 0] (if (> i 0)
                             (if (> i 3) (recur (dec i) (+ s (g i)))
                                 (recur (dec i) (- s (g i)))) s)))]] )

(def region-cases
  (mapv (fn [index [g f]]
          (let [world (w/make-world)
                _ (d/define! world (list 'def 'g g))
                _ (d/define! world (list 'def 'f f))
                ge (cc/compile-def world 'g {:inline-fuel 0})
                fe (cc/compile-def world 'f {:inline-fuel 0})
                gt (regions/typed-function ge {})
                ft (regions/typed-function fe {'g gt})
                id (:value-id (w/entry* (w/snapshot world) 'g))
                name (str "Region" index)]
            (spit (str "experiments/typed_jit/generated/" name ".java")
                  (regions/source name {'g gt 'f ft} 'f id))
            {:class name :f (d/lookup (w/snapshot world) 'f)
             :g-exe ge :f-exe fe :typed ft :id id}))
        (range) region-programs))

(def region-output (doto (io/file "/tmp/klara-s21-classes") .mkdirs))
(assert
 (zero? (.run (javax.tools.ToolProvider/getSystemJavaCompiler) nil System/out System/err
              (into-array String
                          (concat ["-classpath" (System/getProperty "java.class.path")
                                   "-d" (.getPath region-output)
                                   "experiments/typed_jit/Context.java"
                                   "experiments/typed_jit/RegionProbe.java"
                                   "experiments/compiler/java/klara/bench/Baselines.java"]
                                  (map #(str "experiments/typed_jit/generated/" (:class %) ".java")
                                       region-cases))))))
(def region-loader
  (java.net.URLClassLoader. (into-array java.net.URL [(.toURL (.toURI region-output))])
                            (.getContextClassLoader (Thread/currentThread))))
(def context-class (Class/forName "klara.typedprobe.Context" true region-loader))
(defn region-context [id]
  (.newInstance (.getConstructor context-class (into-array Class [String]))
                (object-array [id])))
(defn region-outcome [f]
  (try [:value (f)]
       (catch java.lang.reflect.InvocationTargetException e
         [:error (class (.getCause e)) (.getMessage (.getCause e))])
       (catch Throwable e [:error (class e) (.getMessage e)])))

;; Compare values AND numeric failure class/message to generic T0. No cache scope.
(doseq [{:keys [class f id]} region-cases
        mode ["direct" "inline"]
        :let [cls (Class/forName (str "klara.typedprobe." class) true region-loader)
              method (.getMethod cls mode (into-array Class [context-class Long/TYPE]))]
        n (concat (range -2 16) [Long/MAX_VALUE])]
  (let [expected (region-outcome #(f n))
        actual (region-outcome #(.invoke method nil (object-array [(region-context id) n])))]
    (assert (= expected actual) (pr-str {:class class :mode mode :n n
                                       :expected expected :actual actual}))))
(doseq [{:keys [class id]} region-cases mode ["direct" "inline"]
        :let [cls (Class/forName (str "klara.typedprobe." class) true region-loader)
              method (.getMethod cls mode (into-array Class [context-class Long/TYPE]))]]
  (assert (= IllegalStateException
             (second (region-outcome #(.invoke method nil
                                               (object-array [(region-context "wrong") 20])))))))

;; Unsupported operations and invalid backedges must decline compilation.
(doseq [form ['(fn [n] (/ n 2))
              '(fn [n] (loop [i n] (if (> i 0) (recur 1.5) i)))]]
  (let [world (w/make-world)]
    (d/define! world (list 'def 'bad form))
    (assert (try (regions/typed-function (cc/compile-def world 'bad) {}) false
                 (catch clojure.lang.ExceptionInfo _ true)))))
(println :region-checks-passed {:programs 4 :outcomes 152 :bad-guards 8 :declines 2})

(defn region-bench! []
  (let [{:keys [f g-exe f-exe]} (first region-cases)
        cache (stage/make-cache)
        probe (Class/forName "klara.typedprobe.RegionProbe" true region-loader)]
    (stage/install! cache g-exe)
    (stage/install! cache f-exe)
    (stage/with-cache cache
      (.invoke (.getMethod probe "run" (into-array Class [clojure.lang.IFn]))
               nil (object-array [f])))))
