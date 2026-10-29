(ns kmap.champ-test
  "Model-based test of the clean-room CHAMP against PersistentHashMap,
  including forced full-hash collisions and top-bit-only hash differences."
  (:require [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.generators :as gen]
            [kmap.champ :as champ]
            [kmap.core :as k]))

;; Key with a chosen hasheq; equality by id. Forces collisions.
(deftype CK [id h]
  clojure.lang.IHashEq (hasheq [_] (unchecked-int h))
  Object (hashCode [_] (unchecked-int h))
  (equals [_ o] (and (instance? CK o) (= id (.-id ^CK o))))
  (toString [_] (str "CK" id "/" h)))

(defn ck
  "hash is a function of id (hash contract), chosen to collide."
  [id]
  (CK. id (cond (< id 10) 7                                  ; full collision
                (< id 20) (mod id 3)                         ; collide in low bits
                (< id 30) (bit-shift-left (mod id 4) 30)     ; differ only in bits 30-31
                :else (* 1000003 id))))

(def gen-ck (gen/fmap ck (gen/choose 0 40)))

(def gen-key (gen/one-of [gen-ck (gen/choose -50 50) (gen/fmap bigint (gen/choose -50 50))
                          (gen/elements [:a :b :c nil "x"])]))

(def gen-op (gen/one-of [(gen/tuple (gen/return :assoc) gen-key gen/small-integer)
                         (gen/tuple (gen/return :dissoc) gen-key (gen/return nil))]))

(defn agree? [c m]
  (and (= (count c) (count m))
       (= (k/wrap c) m) (= m (k/wrap c))
       (= (hash (k/wrap c)) (hash m))
       (every? (fn [[kk v]] (= v (get c kk ::nf))) m)
       (= (count (seq c)) (count m))
       (= (set (seq c)) (set (seq m)))))

(def prop-model
  (prop/for-all [ops (gen/vector gen-op 0 200)]
    (loop [c champ/EMPTY m {} [[op kk v] & more :as ops] ops]
      (if (empty? ops)
        (agree? c m)
        (let [c2 (if (= op :assoc) (assoc c kk v) (dissoc c kk))
              m2 (if (= op :assoc) (assoc m kk v) (dissoc m kk))]
          (if (agree? c2 m2) (recur c2 m2 more) false))))))

(deftest champ-model
  (let [r (tc/quick-check 10000 prop-model :max-size 100)]
    (println "quick-check :champ-model" (select-keys r [:pass? :num-tests :seed :time-elapsed-ms])
             (if (:pass? r) "" (pr-str (:smallest (:shrunk r)))))
    (is (:pass? r))))
