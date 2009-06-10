;; Tests

(define print-s
  (lambda ()
    (lambdag@ (s) (begin (write s) (newline) (singleton s)))))

(define nl (string #\newline))

(define (cout . args)
  (for-each (lambda (x)
              (if (procedure? x) (x) (display x)))
            args))

(define errorf
  (lambda (tag . args)
    (printf "Failed: ~s: ~%" tag)
    (apply printf args)
    (error 'WiljaCodeTester "That's all, folks!")))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (cout "Testing " title nl)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
                     "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                     'tested-expression expected produced)))))))

(test-check "test0"
  (run 5 (q)
    (and2
      (== q 1)
      (and2
        (print-s)
        (and2
          (== 2 2)
          (print-s)))))
  `(1))

(test-check "test1"
  (run 5 (q)
    (and2
      (print-s)
      (and2
        (or2
          (== q 1)
          (== q 2))
        (print-s))))
  `(1 2))

(test-check "test2"
  (run 5 (q)
    (existfn (lambda (x) (== x q))))
  `(_.0))

(test-check "test3"
  (run 2 (q)
    (or2
      (== 1 q)
      (or2
        (== 2 q)
        (lambdag@ (s)
          ((lambda (x) (x x))
           (lambda (x) (x x)))))))
  `(1 2))

(test-check "test4"
  (run #f (q)
    (and2
      (== #f q)
      (project q (lambda (q) (== (not (not q)) q)))))
  '(#f))

(test-check "test5"
  (run #f (q)
    (and2
      (== #f q)
      (project q (lambda (y) (== (not (not y)) y)))))
  '(#f))

(test-check "test6"
  (run #f (q)
    (and2
      (== #f q)
      (project q (lambda (q) (== (not (not q)) q)))))
  '(#f))

(test-check "test7"
  (run #f (q)
    (existfn
        (lambda (z)
          (existfn
            (lambda (y)
              (and2
                (== #f y)
                (project z (lambda (z)
                             (and2
                               (== (not (not z)) z)
                               (== `(,y ,z) q))))))))))
  '((#f #t)))

(define anyo
  (lambda (g)
    (or2 g (lambda (s) ((anyo g) s)))))

(test-check "test8"
  (run 5 (q) (anyo (== #f #f)))
  '(_.0 _.0 _.0 _.0 _.0))

(test-check "test9"
  (run 20 (q)
    (and2
      (print-s)
      (or2
       (anyo (== #f #f))
       (and2 (print-s) (anyo (== #t q))))))
  '(_.0 #t _.0 #t _.0 #t _.0 #t _.0 #t _.0 #t _.0 #t _.0 #t _.0 #t _.0 #t))
