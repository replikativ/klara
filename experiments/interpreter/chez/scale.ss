(import (chezscheme))
(define (now) (let ([t (current-time 'time-monotonic)])
  (+ (* (time-second t) 1000000000) (time-nanosecond t))))
(define args (command-line-arguments))
(define mode (string->symbol (car args)))
(define process (cadr args))
(when (eq? mode 'no-cp0) (run-cp0 (lambda (cp0 x) x)))
(compile-interpret-simple #f)
(optimize-level 2)
;; Nested let with sequential generic additions; unique bindings, no macros,
;; parse time excluded. Deliberately linear size, not adversarial expansion.
(for-each (lambda (size)
  (let ([form (let loop ([i 0] [prev 'x] [bindings '()])
                (if (= i size)
                  `(lambda (x) (let* ,(reverse bindings) ,prev))
                  (let ([next (string->symbol (string-append "v" (number->string i)))])
                    (loop (+ i 1) next (cons `(,next (+ ,prev 1)) bindings)))))])
    (do ([sample 0 (+ sample 1)]) [(= sample 5)]
      (let* ([t (now)] [f (compile form)] [elapsed (- (now) t)])
        (unless (= (f 0) size) (error 'scale "bad result" size))
        (printf "~a\t~a\t~a\tcompile-scale\t~a\t~a\t~a\n"
          process mode size sample elapsed (f 0)))))) '(16 64 256 1024))
