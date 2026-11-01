(ns klara.jit.rules
  "The default specializer's own rules (design/09-extensions.md, L4.jit.rules):
  written against the rule interface like any library's, consulted after
  the world's and the preparation's rules.

    classes   a parameter the profile always saw as one array class gets
              the host hint for it under an (instance? C p) guard
              (L4.jit.class-hints)"
  (:require [klara.jit.staged :as staged]
            [klara.stage :refer [code esc lift]]))

(def array-hints
  "Array classes and the host hints that name them (L4.lower.hint): with
   the hint, array access and length compile without reflection."
  {(class (boolean-array 0)) 'booleans (class (byte-array 0)) 'bytes
   (class (char-array 0)) 'chars (class (short-array 0)) 'shorts
   (class (int-array 0)) 'ints (class (long-array 0)) 'longs
   (class (float-array 0)) 'floats (class (double-array 0)) 'doubles
   (class (object-array 0)) 'objects})

(defn- guarded
  "The body with each [i C hint] parameter bound under its hint, inside
   (instance? C p) guards; each guard's fallback is the reference's meaning
   with nothing speculated."
  [ps hinted body fallback]
  (if (empty? hinted)
    (body ps)
    (let [[i c h] (first hinted)
          p (nth ps i)]
      (staged/dynamic
       (klara.jit/guard (code (instance? (esc (lift c)) (esc (staged/->code p))))
                        (staged/->code (staged/let-hinted p h (fn [x] (guarded (assoc ps i x) (rest hinted) body fallback))))
                        (staged/->code (fallback ps)))))))

(def classes
  "L4.jit.class-hints: at a function's entry, the parameters whose
   profile saw a single array class, often enough."
  {:name :classes
   :fn (fn [m]
         (when (= :entry (:point m))
           (let [p (:profile m)
                 hot (:hot (:policy m))
                 hinted (vec (keep-indexed (fn [i c] (when-let [h (get array-hints c)] [i c h])) (:classes p)))]
             (when (and hot (seq hinted) (>= (or (:external p) 0) hot))
               (guarded (:params m) hinted (:body m) (:fallback m))))))})

(def builtin
  "The default specializer's rules, in the order consulted."
  [classes])
