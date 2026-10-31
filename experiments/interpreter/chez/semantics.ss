(import (chezscheme))
(define (check name expected actual)
  (unless (equal? expected actual) (error name "mismatch" expected actual))
  (printf "~s\t~s\n" name actual))
(printf "version\t~s\nmachine\t~s\n" (scheme-version) (machine-type))
(check 'exact-promotes-beyond-long 9223372036854775808 (+ 9223372036854775807 1))
(check 'fixnum-maximum 1152921504606846975 (greatest-fixnum))
(check 'scheme-empty-list-is-true 'true (if '() 'true 'false))
(check 'proper-tail-million 1000000
  ((compile '(lambda (n) (let loop ([i 0]) (if (= i n) i (loop (+ i 1)))))) 1000000))
;; Escape to a fresh receiving continuation on each invocation; captured
;; continuation is reused twice. The box is deliberately shared across shots.
(define saved #f)
(define receiver #f)
(define cell (box 0))
(define (enter thunk) (call/cc (lambda (k) (set! receiver k) (thunk))))
(define first
  (enter (lambda ()
    (let ([x (call/cc (lambda (k) (set! saved k) 10))])
      (set-box! cell (+ (unbox cell) 1))
      (receiver (list x (unbox cell)))))))
(check 'capture-first '(10 1) first)
(check 'resume-first '(20 2) (enter (lambda () (saved 20))))
(check 'resume-second '(30 3) (enter (lambda () (saved 30))))
