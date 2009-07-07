;; Tests

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
    (existfn 'x (lambda (x) (== x q))))
  `(_.0))

(test-check "test8"
  (run 5 (q) (anyo (== #f #f)))
  '(_.0 _.0 _.0 _.0 _.0))


(test-check "test10"
  (run 1 (q)
    (exist (x y z)
      (== `(,x ,y ,z) q)))
  '((_.0 _.1 _.2)))

(test-check "test11"
  (run* (q)
    (conde
      [(== q 1) (== #f #f)]
      [(== q 1) (== #f #t)]
      [(== q 2) (== #t #t)]))
  '(1 2))


(define anyo
  (lambda (g)
    (or2 g (lambdag@ (sk fk s) ((anyo g) sk fk s)))))


(define cc-test
  (lambda (x)
    (and2 (anyo (== x 0)) (== x 1))))

  
