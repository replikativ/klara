(ns klara.account
  "Accounts (design/10-accounting.md, spec/L3-effects.md#accounts).

  Runtime functions of this namespace (the rest is Klara code):
    mint!  spend!  wallet                       the current wallet (L3.account.wallet, L3.account.mint)
    take  spend  split  join  put  holds?  balance  token?   tokens (L3.account.token)

  A receipt's postings are kontor resource transfers in all but their
  accounts and ids; `transfers` fills those in, for an embedding that keeps
  the durable ledger in kontor.")

(defn- decimal-amounts
  "kontor amounts are exact decimals; a ratio without a finite decimal
   expansion cannot be posted and raises."
  [v]
  (into {} (map (fn [[k x]] [(name k) (bigdec x)])) v))

(defn transfers
  "The postings of `receipt` as kontor resource transfers
   (kontor.resource/transfer!): `accounts` maps :parent, :job and :sink to
   the embedding's account references; each transfer's id is derived from
   the receipt's id and the posting's kind, so posting a receipt twice is
   idempotent."
  [receipt accounts]
  (mapv (fn [{:keys [kind source destination resources]}]
          {:id (java.util.UUID/nameUUIDFromBytes (.getBytes (str (:id receipt) "|" (name kind)) "UTF-8"))
           :kind kind
           :source (get accounts source source)
           :destination (get accounts destination destination)
           :resources (decimal-amounts resources)})
        (:postings receipt)))
