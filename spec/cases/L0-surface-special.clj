;; rules: L0.surface.special L0.term.wf
;; expect: [true true [1 2] :two 2 4]
(letfn [(ev? [n] (if (= n 0) true (od? (dec n)))) (od? [n] (if (= n 0) false (ev? (dec n))))]
  [(ev? 10) (od? 7) (let [{:keys [a b] :or {b 2}} {:a 1}] [a b]) (case 2 1 :one 2 :two :other) (cond-> 1 true inc) (-> 5 (- 1))])
