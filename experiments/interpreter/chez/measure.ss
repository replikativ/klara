(import (chezscheme))
(load "experiments/interpreter/chez/workloads.ss")
(define (now) (let ([t (current-time 'time-monotonic)])
  (+ (* (time-second t) 1000000000) (time-nanosecond t))))
(define args (command-line-arguments))
(define action (string->symbol (car args)))
(define mode (string->symbol (cadr args)))
(define process (caddr args))
(define outdir (cadddr args))
(define default-cp0 (run-cp0))
(define (config thunk)
  (parameterize ([optimize-level 2] [compile-interpret-simple #f]
                 [run-cp0 (if (eq? mode 'no-cp0) (lambda (cp0 x) x) default-cp0)])
    (thunk)))
(define (record workload phase sample ns value)
  (printf "~a\t~a\t~a\t~a\t~a\t~a\t~s\n"
    process mode workload phase sample ns value))
(define (checked f n expected)
  (let ([v (f n)]) (unless (equal? v expected) (error 'check "wrong result" v expected)) v))
(define (invoke name f n expected)
  (let* ([t (now)] [v (f n)] [elapsed (- (now) t)])
    (unless (equal? v expected) (error 'first "wrong result" v expected))
    (record name 'first-call 0 elapsed v))
  (do ([i 0 (+ i 1)]) [(= i 200)] (checked f n expected))
  (do ([sample 0 (+ sample 1)]) [(= sample 9)]
    (let* ([t (now)] [v (let loop ([i 0] [last #f])
                       (if (= i 50) last (loop (+ i 1) (f n))))]
           [elapsed (/ (- (now) t) 50.0)])
      (unless (equal? v expected) (error 'warm "wrong result" v expected))
      (record name 'warm-call sample elapsed v))))
(case action
  [(runtime)
   (for-each (lambda (w)
     (let* ([name (car w)] [n (cadr w)] [expected (caddr w)] [form (cadddr w)]
            [t (now)] [f (config (lambda () (compile form)))] [elapsed (- (now) t)])
       (record name 'compile-first 0 elapsed 'ok)
       (invoke name f n expected)
       (do ([i 0 (+ i 1)]) [(= i 9)]
         (let* ([t (now)] [p (config (lambda () (compile form)))] [elapsed (- (now) t)])
           (record name 'compile-repeat i elapsed (procedure? p)))))) workloads)]
  [(aot-build)
   (for-each (lambda (w)
     (let* ([name (car w)] [stem (string-append outdir "/" (symbol->string mode) "-" (symbol->string name))]
            [source (string-append stem ".ss")] [object (string-append stem ".so")])
       (when (file-exists? source) (delete-file source))
       (call-with-output-file source (lambda (p) (write `(define bench ,(cadddr w)) p) (newline p)))
       (let ([t (now)])
         (parameterize ([compile-file-message #f]) (config (lambda () (compile-file source object))))
         (record name 'compile-file 0 (- (now) t) (file-length (open-file-input-port object)))))) workloads)]
  [(aot-run)
   (let* ([name (string->symbol (list-ref args 4))] [w (assq name workloads)]
          [object (string-append outdir "/" (symbol->string mode) "-" (symbol->string name) ".so")]
          [t (now)])
     (load object)
     (record name 'load-object 0 (- (now) t) 'ok)
     (invoke name (top-level-value 'bench) (cadr w) (caddr w)))])
