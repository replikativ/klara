;; Scheme analogues, not a Klara backend. No unsafe operations or fixnum hints.
(define workloads
  '((sum 10000 49995000
      (lambda (n) (let loop ([i 0] [s 0])
        (if (< i n) (loop (+ i 1) (+ s i)) s))))
    (calls 10000 50005000
      (let ([f (lambda (x) (+ x 1))])
        (lambda (n) (let loop ([i 0] [s 0])
          (if (< i n) (loop (+ i 1) (+ s (f i))) s)))))
    (copy-vector 10000 #(49995000 10000)
      (lambda (n) (let loop ([i 0] [a '#(0 0)])
        (if (< i n)
          (loop (+ i 1) (vector (+ (vector-ref a 0) i) (+ (vector-ref a 1) 1))) a))))
    ;; Immutable association-list ledger; keep every version alive, then query
    ;; a past version. 32 accounts, deterministic deposits, no hash-map claim.
    (ledger 1000 (499500 1000 124750)
      (lambda (n)
        (define (put xs key amount)
          (cond [(null? xs) (list (cons key amount))]
                [(= key (caar xs)) (cons (cons key (+ amount (cdar xs))) (cdr xs))]
                [else (cons (car xs) (put (cdr xs) key amount))]))
        (define (total xs) (if (null? xs) 0 (+ (cdar xs) (total (cdr xs)))))
        (let loop ([i 0] [state '()] [versions '()])
          (if (< i n)
            (let ([next (put state (modulo i 32) i)])
              (loop (+ i 1) next (cons next versions)))
            (list (total state) (length versions)
                  (total (list-ref versions (- n 500))))))))))
