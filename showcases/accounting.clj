(ns showcases.accounting
  "Accounting more than memory (design/10-accounting.md).

  A small agent answers questions. Each answer costs money (a model call)
  and needs one of three database connections. The session mints the money
  and the connections; every job gets a budget from its parent's wallet;
  callees get explicit tokens; and every job ends with a receipt whose
  postings could go to kontor as resource transfers."
  (:require [klara.account :as a]
            [klara.job :as job]))

(a/mint! {:eur 10 :db 3})

(defn ask
  "A model call: spends from the token it is given and returns the next
   token with the answer."
  [money question]
  [(a/spend money {:eur 1/4}) (str "answer to " question)])

(defn query
  "Reading the database needs a connection permit."
  [permit q]
  (if (a/holds? permit {:db 1}) [:rows q] (throw (ex-info "no connection" {}))))

(defn answer [question]
  (let [money (a/take {:eur 1})
        permit (a/take {:db 1})
        [money a1] (ask money question)
        [money a2] (ask money (str a1 " with " (query permit question)))]
    (a/put permit)
    (a/put money)
    a2))

(defn careless
  "Uses a token after an operation consumed it."
  [question]
  (let [money (a/take {:eur 1})]
    (ask money question)
    (ask money question)))

(def readers (job/run-all {:budget {:eur 1 :db 1 :steps 10000}}
                          [#(answer "a") #(answer "b") #(answer "c")]))

(def too-many (try (job/run-all {:budget {:eur 1 :db 1}} (vec (repeat 4 #(answer "d"))))
                   (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))

(def mistake (job/run {:budget {:eur 1}} #(careless "e")))

(def receipt (:receipt (first readers)))

{:answers (mapv :value readers)
 :spent-per-answer (dissoc (:spent (first readers)) :steps)
 :fourth-reader too-many
 :mistake (get-in mistake [:error :rule])
 :wallet (a/wallet)
 :balanced (every? #(= (:granted (:receipt %)) (merge-with + (:spent (:receipt %)) (:returned (:receipt %))))
                   (conj readers mistake))
 :kontor (mapv #(dissoc % :id) (a/transfers receipt {:parent "Wallets:Session" :job "Wallets:Answer" :sink "Resources:Consumed"}))}
