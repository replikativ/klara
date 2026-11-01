(ns klara.host.precompile
  "Precompilation from saved profiles (L4.profile.saved): one run records the
  profiles of the program's functions that ran; a later run compiles each
  such definition right after it is defined, with klara.jit and the saved
  profile, so its first call can run compiled code. (Ahead-of-time
  compilation in the design's sense, pinning, is design/02-compilation.md.)

  Host-side driver: the session only offers a hook after each top-level
  form; what to compile and how is klara.jit's."
  (:require [klara.runtime.profile :as profile]
            [klara.runtime.session :as session]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w]))

(defn source-id
  "Identity of a definition's source: SHA-256 of the form as printed with its
   metadata (so ^{:klara/specialize f} counts)."
  [form]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")
        bs (.digest md (.getBytes ^String (binding [*print-meta* true] (pr-str form)) "UTF-8"))]
    (apply str (map #(format "%02x" (bit-and % 0xff)) bs))))

(defn program-namespace?
  "Was namespace `ns` loaded from a file under directory `dir`?"
  [s dir ns]
  (some-> (get-in @s [:ns-sources ns]) (.startsWith (str dir))))

(defn saved-profiles
  "Profiles of the program's function definitions that ran, as EDN data;
   `program?` tells a program namespace from a library."
  [s program?]
  (into {}
        (for [[q d] (w/defs (session/current-world s))
              :let [f (:value d)]
              :when (and (v/closure? f) (program? (symbol (namespace q))))
              :let [p (profile/saved-profile f (source-id (:form d)))]
              :when (pos? (get-in p [:paths [] :count] 0))]
          [q p])))

(defn- compile-defined!
  "After a top-level form: compile what it (re)defined that has a saved
   profile from the same source."
  [saved outcomes]
  (fn [s before]
    (let [after (session/current-world s)]
      (doseq [[q p] saved
              :let [d (w/lookup after q)]
              :when (and d (not= (:generation d) (:generation (w/lookup before q)))
                         (= (:source p) (source-id (:form d))))]
        (let [ns (:ns @s)]
          (session/require-lib! s 'klara.host.precompiled 'klara.jit)
          (swap! s assoc :ns 'klara.host.precompiled)
          (try
            (let [o (session/eval-form s (list 'klara.jit/compile! (list 'quote q) {:profile p}))]
              (swap! outcomes assoc q (:status o)))
            (finally (swap! s assoc :ns ns))))))))

(defn install!
  "Make session `s` compile definitions from `saved` profiles as they are
   defined. Returns an atom of outcomes by name."
  [s saved]
  (let [outcomes (atom {})]
    (swap! s update :after-form (fnil conj []) (compile-defined! saved outcomes))
    outcomes))
