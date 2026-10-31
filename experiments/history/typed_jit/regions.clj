(ns klara.typed-regions
  "S21 probe adapters over the shared scalar analyzer. These narrow adapters
   remain experimental; the staged runtime has its own admission boundary."
  (:require [clojure.string :as str]
            [klara.compile.scalar :as scalar]))

(def fail scalar/fail)
(def typed-function scalar/typed-function)
(def tail-code scalar/tail-code)
(def fresh scalar/fresh)

(defn source [class-name functions entry value-id]
  ;; This experiment's host adapter admits one argument and one world dependency.
  ;; The analyzer is reusable; broader adapters must check all accumulated guards.
  (when-not (and (= [:long] (:args (get functions entry)))
                 (every? #(= [:world 'g value-id] %)
                         (mapcat :dependencies (vals functions))))
    (fail nil "host adapter only supports a unary entry with pinned g"))
  (binding [scalar/*counter* (atom 0)]
    (str "package klara.typedprobe;\npublic final class " class-name " {\n"
         "public static final String G_VALUE_ID = \"" value-id "\";\n"
         (apply str
                (for [[sym f] (sort-by key functions) inline? [false true]
                      :let [params (mapv (fn [_] (fresh)) (:params f))]]
                  (str "public static long " (if inline? "inline_" "direct_") sym "("
                       (str/join "," (map #(str "long " %) params)) ") {\n"
                       (tail-code (:body f) (zipmap (:params f) params) functions inline? nil) "}\n")))
         (apply str
                (for [mode ["direct" "inline"]]
                  (str "public static long " mode "(Context c, long n) {\n"
                       "if (!G_VALUE_ID.equals(c.gValueId())) throw new IllegalStateException(\"guard failed\");\n"
                       "return " mode "_" entry "(n);\n}\n"))) "}\n")))
