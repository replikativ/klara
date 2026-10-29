(ns klara.compile.runtime
  "Direct runtime calls used by K1 emission. Input: an authority operation
  and evaluated arguments; output: its T0 value or exception. Obligation:
  use the same authority store and enclosing branch chain as T0. Control
  operations that create machine frames remain in T0."
  (:require [klara.authority :as a]))

(def authority-ops
  #{:auth/resource :auth/capability :auth/evidence :auth/budget :auth/rand-key
    :auth/consume :auth/payload :auth/draw :auth/spend :auth/remaining
    :auth/split :auth/join :auth/branch :auth/system :auth/merge :auth/discard
    :auth/advance :auth/transfer :auth/partition :auth/status :auth/receipts})

(defn authority-call [ctx op args]
  ;; host-apply places the entry continuation first in *outer-k*. Emitted
  ;; code introduces no authority contexts; all such frames belong to T0.
  (a/op! op args (apply concat (:outer-k ctx))))
