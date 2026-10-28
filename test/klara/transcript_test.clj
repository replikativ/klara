(ns klara.transcript-test
  "Transcript harness: REPL sessions written in markdown are tests.

  A fenced block whose info string starts with `klara-repl` in any
  doc/guide/*.md or examples/**/*.md file holds lines

      k=> <form>
          <continuation of the form, indented by at least 4 spaces>
      <expected output line>
      ...

  The expected output of a form is every line after it (and after its
  continuation lines) up to the next `k=>` line or the end of the
  block; trailing blank lines are ignored. It must equal what
  klara.repl/eval-string prints, exactly. Each file runs in a fresh
  session; the blocks of one file share it, in order. A block tagged
  `klara-repl :norun` is illustrative and not run."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [klara.repl :as repl]))

(def prompt "k=>")

(defn- prompt-line? [l] (or (= l prompt) (str/starts-with? l (str prompt " "))))
(defn- continuation? [l] (str/starts-with? l "    "))

(defn- trim-trailing-blank [lines]
  (vec (reverse (drop-while str/blank? (reverse lines)))))

(defn parse-block
  "Lines of one block (each [line-number text]) -> entries
  {:line n :form text :expected text}, or an {:error ..} entry for
  output before the first prompt."
  [numbered]
  (loop [ls numbered entries [] cur nil]
    (let [close (fn [entries cur]
                  (if cur
                    (conj entries (-> cur
                                      (update :form #(str/join "\n" %))
                                      (update :expected #(str/join "\n" (trim-trailing-blank %)))
                                      (dissoc :in-form?)))
                    entries))]
      (if-let [[n l] (first ls)]
        (cond
          (prompt-line? l)
          (recur (rest ls) (close entries cur)
                 {:line n :form [(subs l (min (count l) (inc (count prompt))))]
                  :expected [] :in-form? true})

          (and cur (:in-form? cur) (continuation? l))
          (recur (rest ls) entries (update cur :form conj l))

          cur
          (recur (rest ls) entries (-> cur (assoc :in-form? false) (update :expected conj l)))

          (str/blank? l) (recur (rest ls) entries cur)

          :else (recur (rest ls) (conj entries {:line n :error (str "output before a prompt: " l)})
                       cur))
        (close entries cur)))))

(defn parse-file
  "Markdown text -> blocks [{:line n :norun? b :entries [..]}]."
  [text]
  (let [lines (map-indexed (fn [i l] [(inc i) l]) (str/split-lines text))]
    (loop [ls lines blocks [] open nil]
      (if-let [[n l] (first ls)]
        (let [t (str/trim l)]
          (cond
            (and (nil? open) (str/starts-with? t "```"))
            (let [info (str/split (str/trim (subs t 3)) #"\s+")]
              (recur (rest ls) blocks {:line n :tag (first info) :opts (set (rest info)) :lines []}))

            (and open (str/starts-with? t "```"))
            (recur (rest ls)
                   (if (= "klara-repl" (:tag open))
                     (conj blocks {:line (:line open)
                                   :norun? (contains? (:opts open) ":norun")
                                   :entries (parse-block (:lines open))})
                     blocks)
                   nil)

            open (recur (rest ls) blocks (update open :lines conj [n l]))
            :else (recur (rest ls) blocks nil)))
        blocks))))

(defn transcript-files
  "doc/guide/*.md and examples/**/*.md under root, sorted."
  ([] (transcript-files "."))
  ([root]
   (let [guide (io/file root "doc" "guide")
         ex (io/file root "examples")
         md? #(and (.isFile ^java.io.File %) (str/ends-with? (.getName ^java.io.File %) ".md"))]
     (sort-by str
              (concat (when (.isDirectory guide) (filter md? (.listFiles guide)))
                      (when (.isDirectory ex) (filter md? (file-seq ex))))))))

(defn run-file
  "Run every checked block of a markdown file in one fresh session.
  Returns results [{:line n :form .. :expected .. :actual ..}]."
  [file]
  (let [s (repl/session)]
    (vec (for [b (parse-file (slurp file))
               :when (not (:norun? b))
               e (:entries b)]
           (if (:error e)
             (assoc e :actual nil)
             (assoc e :actual (repl/eval-string s (:form e))))))))

(deftest parser
  (let [md (str "text\n```klara-repl\nk=> (+ 1 2)\n3\nk=> (let [x 1]\n"
                "        x)\n1\n\nk=> :repl/basis\nmain v0\n```\n"
                "```klara-repl :norun\nk=> (oops)\n```\n```clojure\nk=> no\n```\n")
        [b1 b2 :as bs] (parse-file md)]
    (is (= 2 (count bs)))
    (is (= [{:line 3 :form "(+ 1 2)" :expected "3"}
            {:line 5 :form "(let [x 1]\n        x)" :expected "1"}
            {:line 9 :form ":repl/basis" :expected "main v0"}]
           (:entries b1)))
    (is (:norun? b2))
    (testing "the parsed block runs"
      (let [s (repl/session)]
        (is (= ["3" "1" "main v0"] (map #(repl/eval-string s (:form %)) (:entries b1))))))))

(deftest transcripts
  (doseq [f (transcript-files)]
    (testing (str f)
      (doseq [{:keys [line form expected actual error]} (run-file f)]
        (if error
          (is false (str f ":" line ": " error))
          (is (= expected actual)
              (str f ":" line ": k=> " form)))))))
