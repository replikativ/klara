(ns klara.residual)

;; One traversal over the inspected fragment. The backend and scope checker
;; retain authority over structure/binders; the generator sees descriptions.
(defn regenerate [source]
  (let [view (perform :stage/inspect source)
        nodes (get view :nodes)]
    (letfn [(children [ids]
              (loop [i 0 result []]
                (if (< i (count ids))
                  (recur (inc i) (conj result (visit (nth ids i)))) result)))
            (visit [id]
              (let [node (nth nodes id)]
                (perform :stage/rebuild (get node :at)
                         (children (get node :children)))))]
      (visit (get view :root)))))

;; New bindings come from a closed Code template, not invented variable names.
;; This constructs a new function with an explicitly requested postprocessing
;; body. It is not an automatic proof that it equals the original function.
(defn postprocess [source template]
  (let [view (perform :stage/inspect source)
        nodes (get view :nodes)
        root (nth nodes (get view :root))]
    (if (= (get root :op) :fn)
      (let [body (nth nodes (nth (get root :children) 0))
            replacement (perform :stage/compose (get body :at) template [(get body :code)])]
        (perform :stage/rebuild (get root :at) [replacement]))
      (perform :exn/raise "postprocess requires function Code"))))

;; A deliberately small semantic rule: a literal conditional test evaluates
;; without effects or failure. Only nil and false are false in Klara.
;; No arithmetic is executed during rewriting, and no let is floated.
(defn prune-literal-branches [source]
  (let [view (perform :stage/inspect source)
        nodes (get view :nodes)]
    (letfn [(children [ids]
              (loop [i 0 result []]
                (if (< i (count ids))
                  (recur (inc i) (conj result (visit (nth ids i)))) result)))
            (visit [id]
              (let [node (nth nodes id) ids (get node :children)]
                (if (= (get node :op) :if)
                  (let [test (nth nodes (nth ids 0))]
                    (if (= (get test :op) :quote)
                      (visit (nth ids (if (get test :datum) 1 2)))
                      (perform :stage/rebuild (get node :at) (children ids))))
                  (perform :stage/rebuild (get node :at) (children ids)))))]
      (visit (get view :root)))))
