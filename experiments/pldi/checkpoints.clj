;; Additional format-level coverage beyond compiler-emitted source positions.
;; Run only after joining the preceding JVM, via run.py.
(require '[clojure.test :as t] '[klara.deopt-test] '[klara.compile.speculate-test]
         '[klara.compile.unbox-test] '[klara.compile.direct-abi-test]
         '[klara.defs :as d] '[klara.world :as w] '[klara.eval :as ev]
         '[klara.stage :as s] '[klara.authority :as a])
(def events (atom []))
(def original-record s/record-deopt!)
(defn recorder [cache exe fs live]
  (swap! events conj {:tests (mapv #(str (:ns (meta %)) "/" (:name (meta %))) t/*testing-vars*)
                     :code-id (:code-id exe) :frame-state fs
                     :live-kinds (mapv #(some-> % class .getName) live)})
  (original-record cache exe fs live))
(defn manual-frame [tag body]
  (let [wo (w/make-world)
        _ (d/define! wo (list 'def 'f (list 'fn '[x probe]
                                          (list 'let ['seen '(count probe)] body))))
        root (w/snapshot wo) f (d/lookup root 'f)
        frame {:site tag :at [:ret [:live 0]]
               :env [[:live 0] [:live 1] [:live 2]]
               :kont [{:tag tag :path [:body :body] :env 3}]}
        fast (fn [x probe] (let [seen (count probe)] (ev/deopt! 0 [x probe seen])))
        exe (s/speculative f fast [frame] #{[:captures []]} {:author :s16-format-injection})]
    (doseq [x [1 1.5 false nil :bad]]
      (let [observe (fn [cache]
                      (let [trace (atom []) probe (reify clojure.lang.Counted
                                                  (count [_] (swap! trace conj :prefix) 1))
                            result (try [:value (s/with-cache cache (f x probe))]
                                        (catch Exception e [:error (class e) (ex-message e)]))]
                        [result @trace]))
            cache (doto (s/make-cache) (s/install! exe))]
        (assert (= (observe (s/make-cache)) (observe cache)) [tag x])
        (assert (= 1 (:deopts (s/stats cache))) [tag x])))))
(let [out (first *command-line-args*)
      summary (with-redefs [s/record-deopt! recorder]
                (manual-frame :let '(let [y x] (+ y 1)))
                (manual-frame :if '(if x 1 2))
                (t/run-tests 'klara.deopt-test 'klara.compile.speculate-test
                             'klara.compile.unbox-test 'klara.compile.direct-abi-test))
      slots (mapcat (fn [e]
                      (let [fs (:frame-state e)]
                        (tree-seq coll? seq [(:env fs) (second (:at fs))
                                              (mapv #(select-keys % [:env :vals :clauses :instance :return]) (:kont fs))])))
                    @events)
      descriptors (set (keep #(when (and (vector? %) (#{:live :const :local :closure :letrec :instance :vector} (first %)))
                               (first %)) slots))
      tags (set (mapcat #(map :tag (get-in % [:frame-state :kont])) @events))
      modes (set (map #(first (get-in % [:frame-state :at])) @events))]
  (assert (zero? (+ (:fail summary) (:error summary))))
  (assert (= #{:let :if :list :handle} tags) tags)
  (assert (= #{:eval :ret} modes) modes)
  (assert (= #{:live :const :local :closure :letrec :instance :vector} descriptors) descriptors)
  (spit (str out "/checkpoint-inventory.edn")
        (pr-str {:summary summary :event-count (count @events) :frame-tags tags
                 :resume-modes modes :descriptors descriptors :events @events}))
  (prn {:events (count @events) :frame-tags tags :resume-modes modes :descriptors descriptors}))
(shutdown-agents)
