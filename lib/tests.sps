(import (minikanren nominal-disequality)
  (rnrs) (rnrs eval))

#| look for more tests in files in /home/ramana/fmk and /home/ramana/Papers/* |#

(define-syntax define-missing-exports
  (lambda (o)
    (define unbound?
      (let ((empty-ctxt (car (generate-temporaries '(t)))))
        (lambda (id)
          (let ((unbound-id (datum->syntax empty-ctxt (syntax->datum id))))
            (free-identifier=? id unbound-id)))))
    (syntax-case o ()
      ((_ id ...)
       #`(begin .
           #,(let rec ((ls #'(id ...)))
               (cond
                 ((null? ls) '())
                 ((unbound? (car ls))
                  (cons
                    #`(define-syntax #,(car ls)
                        (lambda (o)
                          (syntax-case o ()
                            (_ #'(raise (symbol->string '#,(car ls)))))))
                    (rec (cdr ls))))
                 (else (rec (cdr ls))))))))))

(define-missing-exports
  run run* run+ conde exist ==
  fresh hash tie ==-check ==-no-check
  =/= tabled pa/ir project)

(define-syntax multi (syntax-rules () ((_ x . b) (exist () . b)))) ; multi is deprecated... for now

(define remove-answer
  (lambda (x ls)
    (cond
      ((null? ls) '())
      ((equal? (car ls) x) (cdr ls))
      (else (cons (car ls) (remove-answer x (cdr ls)))))))

(define answer-set-equal?
  (lambda (ls1 ls2)
    (cond
      ((null? ls1) (null? ls2))
      ((member (car ls1) ls2)
       (answer-set-equal? (cdr ls1) (remove-answer (car ls1) ls2)))
      (else #f))))

(define skipped-tests
  (let ((ls '()))
    (case-lambda
      (() ls)
      ((t) (set! ls (cons t ls))))))

(define-syntax print
  (syntax-rules (nl)
    ((_ nl . x) (begin (newline) (print . x)))
    ((_ x0 . x) (begin (display x0) (print . x)))
    ((_) (values))))

(define-syntax define-test
  (syntax-rules ()
    ((_ name (pl ...) expr (pr ...) (do-name args ...))
     (define-syntax name
       (syntax-rules (skip)
         ((_ title (skip reason) pl ... expr pr ...)
          (let ((t title) (r reason)) (print "SKIPPING " t ": " r nl) (skipped-tests (cons t r))))
         ((_ title skip pl ... expr pr ...) (name title (skip "no reason") pl ... expr pr ...))
         ((_ title pl ... expr pr ...)
          (let ((t title))
            (guard (con
                     ((string? con)
                      (let ((r (string-append "no " con)))
                        (print " SKIPPING: " r nl)
                        (skipped-tests (cons t r)))))
              (let ((th (lambda () expr)))
                (print "Testing " t "...")
                (do-name th args ... (lambda (string . irr) (apply error 'title string 'expr irr)))
                (print " done" nl))))))))))

(define-syntax define-dtest
  (lambda (o)
    (syntax-case o ()
      ((_ dtest do-dtest)
       (guard (con (else #f)) (environment '(scheme)))
       #'(begin
           (define do-dtest
             (let ((make-engine (eval 'make-engine (environment '(scheme))))
                   (max-ticks (exact 1e8)))
               (lambda (th error)
                 ((make-engine th)
                  max-ticks
                  (lambda (t v) (error "failed to diverge" (- max-ticks t) v))
                  (lambda (e) (values))))))
           (define-test dtest () expr () (do-dtest))))
      ((_ dtest _)
       #'(define-syntax dtest
           (syntax-rules ()
             ((_ title . _) (test title (skip "no engines") #f #f))))))))

(define-test test () expr (expe) (do-test expe equal?))
(define-test mtest () expr (expe) (do-test expe answer-set-equal?))
(define-test ptest (passes?) expr () (do-test 'ptest (lambda (e c) (passes? c))))
(define-test ftest () expr (expe) (do-ftest expe))
(define-test vtest (pred?) expr () (do-vtest pred?))
(define-dtest dtest do-dtest)

(define do-test
  (lambda (th expected equal? error)
    (let ((computed (th)))
      (unless (equal? expected computed)
        (print nl "expected: " expected)
        (print nl "computed: " computed nl)
        (error "failed")))))

(define do-ftest
  (lambda (th expe error)
    (unless (null? expe)
      (let ((p (th)))
        (cond
          ((null? p) (error "failed to produce answers" expe))
          ((member (car p) expe) (do-ftest (cdr p) (remove-answer (car p) expe) error))
          (else (do-ftest (cdr p) expe error)))))))

(define do-vtest
  (lambda (th pred? error)
    (guard
      (con
        ((pred? con))
        (else (error "failed to produce appropriate error" con)))
      (begin (th) (error "no error")))))

(test 'tied-pair1
  (run* (q)
    (fresh (a b)
      (exist (w x y z)
        (pa/ir x)
        (== (tie a y) (tie b z))
        (== x y)
        (== w (cons #t #f))
        (== y w))))
  '())

(test 'unify-tie
  (run* (q)
    (fresh (a)
      (exist (x y)
        (== (tie a x) (tie a a))
        (hash a x))))
  '())

(test 'hash-check
  (run* (q)
    (exist (first rest t)
      (fresh (a)
        (hash a t)
        (== first a)
        (== `(,first . ,rest) t))))
  '())

(test 'hash-check1
  (run* (q)
    (fresh (a b)
      (exist (x y t)
        (hash a x)
        (== (tie a t) (tie b y))
        (== x t)
        (== y b))))
  '())

(test 'fresh0
  (run* (q)
    (fresh (a)
      (== a a)))
  '(_.0))

(test 'fresh1
  (run* (q)
    (fresh (a)
      (== a 5)))
  '())

(test 'fresh2
  (run* (q)
    (fresh (a b)
      (== a b)))
  '())

(test 'fresh3
  (run* (q)
    (fresh (b)
      (== b q)))
  '(a.0))

(test 'fresh4
  (run* (q)
    (exist (x y z)
      (fresh (a)
        (== x a)
        (fresh (a b)
          (== y a)
          (== `(,x ,y ,z ,a ,b) q)))))
  '((a.0 a.1 _.0 a.1 a.2)))

(test 'tie1
  (run* (q)
    (fresh (a b)
      (== (tie a `(foo ,a 3 ,b)) q)))
  '((tie a.0 (foo a.0 3 a.1))))

(test 'hash0
  (run* (q)
    (fresh (a)
      (== `(3 ,a #t) q)
      (hash a q)))
  '())

(test 'hash1
  (run* (q)
    (fresh (a)
      (hash a q)
      (== `(3 ,a #t) q)))
  '())

(test 'hash2
  (run* (q)
    (fresh (a b)
      (hash a (tie b a))))
  '())

(test 'hash3
  (run* (q)
    (fresh (a b)
      (hash a (tie a a))))
  '(_.0))

(test 'hash4
  (run* (q)
    (exist (x y z)
      (fresh (a)
        (hash a x)
        (== `(,y ,z) x)
        (== `(,x ,a) q))))
  '((((_.0 _.1) a.0) (hash (a.0 . (_.0 _.1))))))

(test 'unify-tie1
  (run* (q)
    (fresh (a b)
      (== (tie a a) (tie b b))))
  '(_.0))

(test 'unify-tie2
  (run* (q)
    (fresh (a b)
      (exist (x y)
        (== (tie a (tie a x)) (tie a (tie b y)))
        (== `(,x ,y) q))))
  `((((sus ((a.0 . a.1)) _.0) _.0) (hash (a.0 . (_.0))))))

(test 'unify-tie3
  (run* (q)
    (fresh (a b)
      (exist (x y)
        (conde
          [(== (tie a (tie b `(,x ,b))) (tie b (tie a `(,a ,x))))]
          [(== (tie a (tie b `(,y ,b))) (tie b (tie a `(,a ,x))))]
          [(== (tie a (tie b `(,b ,y))) (tie b (tie a `(,a ,x))))]
          [(== (tie a (tie b `(,b ,y))) (tie a (tie a `(,a ,x))))])
        (== q `(,x ,y)))))
  '((a.0 a.1)
    (_.0 (sus ((a.0 . a.1)) _.0))
    ((_.0 (sus ((a.0 . a.1)) _.0)) (hash (a.0 . (_.0))))))

(test 'type1
      (run* (q)
        (exist (t u)
          (fresh (a b c d)
            (== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
            (== `(lam ,(tie c `(lam ,(tie d `(var ,c))))) u)
            (== t u))))
      '(_.0))

(test 'type2
      (run* (q)
        (exist (t u)
          (fresh (a b c d)
            (== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
            (== `(lam ,(tie c `(lam ,(tie d `(var ,d))))) u)
            (== t u))))
      '())

(letrec ((substo
           (lambda (e new a out)
             (conde
               [(== `(var ,a) e) (== new out)]
               [(exist (y)
                  (== `(var ,y) e)
                  (== `(var ,y) out)
                  (hash a y))]
               [(exist (rator ratorres rand randres)
                  (== `(app ,rator ,rand) e)
                  (== `(app ,ratorres ,randres) out)
                  (substo rator new a ratorres)
                  (substo rand new a randres))]
               [(exist (body bodyres)
                  (fresh (c)
                    (== `(lam ,(tie c body)) e)
                    (== `(lam ,(tie c bodyres)) out)
                    (hash c a)
                    (hash c new)
                    (substo body new a bodyres)))]))))

  (test 'substo1
    (run* (q)
      (fresh (a b)
        (substo `(lam ,(tie a `(app (var ,a) (var ,b))))
          `(var ,b) a q)))
    '((lam (tie a.0 (app (var a.0) (var a.1))))))

  (test 'substo2
    (run* (x)
      (fresh (a b)
        (substo `(lam ,(tie a `(var ,b)))
          `(var ,a) b x)))
    '((lam (tie a.0 (var a.1))))))

(letrec ((typo
           (lambda (g e te)
             (conde
               [(exist (x)
                  (== `(var ,x) e)
                  (lookupo x te g))]
               [(exist (rator trator rand trand)
                  (== `(app ,rator ,rand) e)
                  (== `(arr ,trand ,te) trator)
                  (typo g rator trator)
                  (typo g rand trand))]
               [(exist (e^ te^ trand g^)
                  (fresh (b)
                    (== `(lam ,(tie b e^)) e)
                    (== `(arr ,trand ,te^) te)
                    (hash b g)
                    (== `((,b . ,trand) . ,g) g^)
                    (typo g^ e^ te^)))])))

         (lookupo
           (lambda (x tx g)
             (exist (a d)
               (== `(,a . ,d) g)
               (conde
                 [(==-check `(,x . ,tx) a)]
                 [(exist (x^ tx^)
                    (== `(,x^ . ,tx^) a)
                    (hash x x^)
                    (lookupo x tx d))])))))

  (test 'typo1
    (run* (q)
      (fresh (c d)
        (typo '() `(lam ,(tie c `(lam ,(tie d `(var ,c))))) q)))
    '((arr _.0 (arr _.1 _.0))))

  (test 'typo2
    (run* (q)
      (fresh (c)
        (typo '() `(lam ,(tie c `(app (var ,c) (var ,c)))) q)))
    '())

  (test 'typo3
    (run 2 (q)
      (typo '() q '(arr int int)))
    '((lam (tie a.0 (var a.0)))
      (lam (tie a.0 (app (lam (tie a.1 (var a.1))) (var a.0)))))))

(test 'acab-0
  (run* (q)
    (fresh (a b c)
      (== (tie b (tie c b)) (tie a (tie b a)))))
  '(_.0))

(test 'acab-1
  (run* (q)
    (fresh (a b c)
      (== q a)
      (== (tie b (tie c b)) (tie a (tie b q)))))
  '(a.0))

(test 'acab-2
  (run* (q)
    (fresh (a b c)
      (== (tie b (tie c b)) (tie a (tie b q)))
      (== q a)))
  '(a.0))

(test 'acab-3
  (run* (q)
    (fresh (a b c)
      (== (tie b (tie c b)) (tie a (tie b q)))))
  '(a.0))

(mtest "pa/ir-0"
  (run* (q) (pa/ir q))
  '((_.0 (pa/ir _.0))))

(test "pa/ir-1"
  (run* (q) (pa/ir q) (== 9 q))
  '(9))

(test "pa/ir-2"
  (run* (q) (== 9 q) (pa/ir q))
  '(9))

(test "pa/ir-3"
  (run* (q) (== #t #t))
  '(_.0))

(mtest "pa/ir-4"
  (run* (q)
    (exist (x y)
      (pa/ir x)
      (pa/ir q)
      (pa/ir y)))
  '((_.0 (pa/ir _.0))))

(test "pa/ir-5"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (pa/ir x)
      (pa/ir q)
      (pa/ir y)))
  '())

(test "pa/ir-6"
  (run* (q)
    (exist (x y)
      (pa/ir x)
      (pa/ir q)
      (pa/ir y)
      (== `(,x ,y) q)))
  '())

(mtest "pa/ir-7"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (pa/ir x)
      (pa/ir y)))
  '(((_.0 _.1) (pa/ir _.0 _.1))))

(test "pa/ir-8"
  (run* (q)
    (exist (x)
      (pa/ir x)
      (== '() x)))
  '(_.0))

(test "pa/ir-9"
  (run* (q)
    (exist (x)
      (== '() x)
      (pa/ir x)))
  '(_.0))

(test "pa/ir-10"
  (run* (q)
    (exist (x)
      (== '(3 . 5) x)
      (pa/ir x)))
  '())

(test "pa/ir-11"
  (run* (q)
    (exist (x)
      (pa/ir x)
      (== '(3 . 5) x)))
  '())

(mtest "pa/ir-12"
  (run* (q)
    (pa/ir q)
    (pa/ir q))
  '((_.0 (pa/ir _.0))))

(test 'pa/ir1
  (run* (q)
    (exist (a d)
      (== q `(,a . ,d))
      (pa/ir q)))
  '())

(test 'pa/ir2
  (run* (q)
    (exist (x)
      (pa/ir q)
      (== q x)
      (== x '(3 4))))
  '())

(mtest 'pa/ir3
  (run* (q)
    (exist (x)
      (== q x)
      (pa/ir q)))
  '((_.0 (pa/ir _.0))))

(test 'pa/ir4
  (run* (q)
    (exist (a d)
      (pa/ir a)
      (pa/ir q)
      (== a 3)
      (== q `(,a . ,d))
      (pa/ir d)))
  '())

(mtest "pa/ir conde 0"
  (run* (q)
    (exist (x)
      (conde
        ((== q x) (pa/ir x))
        ((== q 0) (pa/ir x)))))
  '((_.0 (pa/ir _.0))
    0))

(mtest "pa/ir =/= conde"
  (run* (q)
    (exist (x)
      (conde
        ((== q x) (pa/ir x))
        ((== q 0) (=/= x 0) (pa/ir x)))))
  '((_.0 (pa/ir _.0))
    0))

(mtest "=/= pa/ir q"
  (run* (q)
    (pa/ir q)
    (=/= q '(p)))
  '((_.0 (pa/ir _.0))))

(mtest "never-equalo-1"
  (run* (q)
    (=/= 3 q)
    (== q 3))
  '())

(mtest "never-equalo-2"
  (run* (q)
    (== q 3)
    (=/= 3 q))
  '())

(mtest "never-equalo-3"
  (run* (q)
    (exist (x y)
      (=/= x y)
      (== x y)))
  '())

(mtest "never-equalo-4"
  (run* (q)
    (exist (x y)
      (== x y)
      (=/= x y)))
  '())

(mtest "never-equalo-5"
  (run* (q)
    (exist (x y)
      (=/= x y)
      (== 3 x)
      (== 3 y)))
  '())

(mtest "never-equalo-6"
  (run* (q)
    (exist (x y)
      (== 3 x)
      (=/= x y)
      (== 3 y)))
  '())

(mtest "never-equalo-7"
  (run* (q)
    (exist (x y)
      (== 3 x)
      (== 3 y)
      (=/= x y)))
  '())

(mtest "never-equalo-8"
  (run* (q)
    (exist (x y)
      (== 3 x)
      (== 3 y)
      (=/= y x)))
  '())

(mtest "never-equalo-9"
  (run* (q)
    (exist (x y z)
      (== x y)
      (== y z)
      (=/= x 4)
      (== z (+ 2 2))))
  '())

(mtest "never-equalo-10"
  (run* (q)
    (exist (x y z)
      (== x y)
      (== y z)
      (== z (+ 2 2))
      (=/= x 4)))
  '())

(mtest "never-equalo-11"
  (run* (q)
    (exist (x y z)
      (=/= x 4)
      (== y z)
      (== x y)
      (== z (+ 2 2))))
  '())

(mtest "never-equalo-12"
  (run* (q)
    (exist (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '(_.0))

(mtest "never-equalo-13"
  (run* (q)
    (exist (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (== z 1)
      (== `(,x ,y) q)))
  '())

(mtest "never-equalo-14"
  (run* (q)
    (exist (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (== z 0)))
  '(_.0))

(mtest "never-equalo-15"
  (run* (q)
    (exist (x y z)
      (== z 0)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '(_.0))

(mtest "never-equalo-16"
  (run* (q)
    (exist (x y z)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (=/= x y)))
  '(_.0))

(mtest "never-equalo-17"
  (run* (q)
    (exist (x y z)
      (== z 1)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '())

(mtest "never-equalo-18"
  (run* (q)
    (exist (x y z)
      (== z 1)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (=/= x y)))
  '())

(mtest "never-equalo-19"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)))
  '(_.0))

(mtest "never-equalo-20"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== y 1)))
  '(_.0))

(mtest "never-equalo-21"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 1)))
  '())

(mtest "never-equalo-22"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== `(,x ,y) q)))
  '(((_.0 _.1) (=/= ((_.0 . 2) (_.1 . 1))))))

(mtest "never-equalo-23"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== `(,x ,y) q)))
  '(((2 _.0) (=/= ((_.0 . 1))))))

(mtest "never-equalo-24"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 9)
      (== `(,x ,y) q)))
  '((2 9)))

(mtest "never-equalo-25"
  (run* (q)
    (exist (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 1)
      (== `(,x ,y) q)))
  '())

(mtest "never-equalo-26"
  (run* (q)
    (exist (a x z)
      (=/= a `(,x 1))
      (== a `(,z 1))
      (== x z)))
  '())

(mtest "never-equalo-27"
  (run* (q)
    (exist (a x z)
      (=/= a `(,x 1))
      (== a `(,z 1))
      (== x 5)
      (== `(,x ,z) q)))
  '(((5 _.0) (=/= ((_.0 . 5))))))

(mtest "never-equalo-28"
  (run* (q)
    (=/= 3 4))
  '(_.0))

(mtest "never-equalo-29"
  (run* (q)
    (=/= 3 3))
  '())

(mtest "never-equalo-30"
  (run* (q)
    (exist (a)
      (=/= a 3)
      (== 3 a)))
  '())

(mtest "never-equalo-31"
  (run* (q)
    (exist (a)
      (== 3 a)
      (=/= a 3)))
  '())

(mtest "never-equalo-32"
  (run* (q)
    (exist (a)
      (== 3 a)
      (=/= a 4)))
  '(_.0))

(mtest "never-equalo-33"
  (run* (q)
    (=/= 4 q)
    (=/= 3 q))
  '((_.0 (=/= ((_.0 . 4)) ((_.0 . 3))))))

(mtest "never-equalo-34"
  (run* (q) (=/= q 5) (=/= q 5))
  '((_.0 (=/= ((_.0 . 5))))))

(mtest "never-equalo-35"
  (let ((foo (lambda (x)
               (exist (a)
                 (=/= x a)))))
    (run* (q) (exist (a) (foo a))))
  '(_.0))

(mtest "never-equalo-36"
  (let ((foo (lambda (x)
               (exist (a)
                 (=/= x a)))))
    (run* (q) (exist (b) (foo b))))
  '(_.0))

(mtest "never-equalo-37"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= x y)))
  '(((_.0 _.1) (=/= ((_.0 . _.1))))))

(mtest "never-equalo-38"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= y x)))
  '(((_.0 _.1) (=/= ((_.1 . _.0))))))

(mtest "never-equalo-39"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= x y)
      (=/= y x)))
  '(((_.0 _.1) (=/= ((_.0 . _.1))))))

(mtest "never-equalo-40"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= x y)
      (=/= x y)))
  '(((_.0 _.1) (=/= ((_.0 . _.1))))))

(mtest "never-equalo-41"
  (run* (q) (=/= q 5) (=/= 5 q))
  '((_.0 (=/= ((_.0 . 5))))))

(mtest "never-equalo-42"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= `(,x ,y) `(5 6))
      (=/= x 5)))
  '(((_.0 _.1) (=/= ((_.0 . 5))))))

(mtest "never-equalo-43"
  (run* (q)
    (exist (x y)
      (== `(,x ,y) q)
      (=/= x 5)
      (=/= `(,x ,y) `(5 6))))
  '(((_.0 _.1) (=/= ((_.0 . 5))))))

(mtest "never-equalo-44"
  (run* (q)
    (exist (x y)
      (=/= x 5)
      (=/= `(,x ,y) `(5 6))
      (== `(,x ,y) q)))
  '(((_.0 _.1) (=/= ((_.0 . 5))))))

(mtest "never-equalo-45"
  (run* (q)
    (exist (x y)
      (=/= 5 x)
      (=/= `(,x ,y) `(5 6))
      (== `(,x ,y) q)))
  '(((_.0 _.1) (=/= ((_.0 . 5))))))

(mtest "never-equalo-46"
  (run* (q)
    (exist (x y)
      (=/= 5 x)
      (=/= `( ,y ,x) `(6 5))
      (== `(,x ,y) q)))
  '(((_.0 _.1) (=/= ((_.0 . 5))))))

(mtest "never-equalo-47"
  (run* (x)
    (exist (y z)
      (=/= x `(,y 2))
      (== x `(,z 2))))
  '((_.0 2)))

(mtest "never-equalo-48"
  (run* (x)
    (exist (y z)
      (=/= x `(,y 2))
      (== x `((,z) 2))))
  '(((_.0) 2)))

(mtest "never-equalo-49"
  (run* (x)
    (exist (y z)
      (=/= x `((,y) 2))
      (== x `(,z 2))))
  '((_.0 2)))

(mtest "pa/ir-0"
  (run* (q)
    (pa/ir 3))
  '(_.0))

(mtest "pa/ir-1"
  (run* (q)
    (pa/ir '(3 4)))
  '())

(mtest "pa/ir-2"
  (run* (q)
    (exist (x)
      (== x '(3 . 4))
      (pa/ir x)))
  '())

(mtest "pa/ir-3"
  (run* (q)
    (exist (x)
      (pa/ir x)
      (== x '(3 . 4))))
  '())

(mtest "pa/ir-4"
  (run* (q)
    (exist (x y)
      (pa/ir q)
      (== q x)
      (== y `(,q . ,x))))
  '((_.0 (pa/ir _.0))))

(mtest "pa/ir-5"
  (run* (q)
    (exist (x)
      (== q x)
      (pa/ir x)
      (== q '(3))))
  '())

(mtest "pa/ir-6"
  (run* (q)
    (exist (x)
      (== q x)
      (pa/ir x)
      (== q '())))
  '(()))

(mtest "pa/ir-7"
  (run* (q)
    (pa/ir q))
  '((_.0 (pa/ir _.0))))

(mtest "pa/ir-8"
  (run* (q)
    (exist (x)
      (pa/ir x)))
  '(_.0))

(mtest "pa/ir-9"
  (run* (q)
    (exist (x)
      (pa/ir x)
      (== q `(,x))))
  '(((_.0) (pa/ir _.0))))

(mtest "pa/ir-10"
  (run* (q)
    (pa/ir q)
    (pa/ir q))
  '((_.0 (pa/ir _.0))))

(mtest "pa/ir-11"
  (run* (q)
    (exist (x y z)
      (pa/ir z)
      (== q `(,x ,y ,z))
      (pa/ir y)))
  '(((_.0 _.1 _.2) (pa/ir _.1 _.2))))

(mtest "pa/ir-12"
  (run* (q)
    (exist (x y z)
      (== q `(,x ,y ,z))
      (pa/ir y)
      (pa/ir z)))
  '(((_.0 _.1 _.2) (pa/ir _.1 _.2))))

(mtest "pa/ir =/= 0"
  (run* (q)
    (exist (x y)
      (pa/ir x)
      (=/= x y)
      (== q `(,x ,y))))
  '(((_.0 _.1) (=/= ((_.0 . _.1))) (pa/ir _.0))))

(mtest "pa/ir =/= 1"
  (run* (q)
    (exist (x y)
      (pa/ir x)
      (=/= y x)
      (=/= x y)
      (== q `(,x ,y))
      (pa/ir x)))
  '(((_.0 _.1) (=/= ((_.0 . _.1))) (pa/ir _.0))))

(mtest "pa/ir =/= 2"
  (run* (q)
    (exist (x y)
      (conde
        ((== q `(,x ,y))
         (pa/ir x)
         (=/= y 10))
        ((=/= x 5))
        ((pa/ir q)
         (=/= x 5))
        ((pa/ir y)
         (== q `(,y . ,x))
         (=/= q x)
         (=/= x y)))))
  '(((_.0 _.1) (=/= ((_.1 . 10))) (pa/ir _.0))
    _.0
    (_.0 (pa/ir _.0))
    ((_.0 . _.1) (=/= ((_.1 . _.0))) (pa/ir _.0))))

(mtest "pa/ir =/= 3"
  (run* (q)
    (exist (x y)
      (conde
        ((== q `(,x ,y))
         (pa/ir y))
        ((== q `(,x ,y))
         (pa/ir q))
        ((== q `(,x ,y))
         (=/= x y)
         (pa/ir y))
        ((== q `(,x ,y))
         (=/= x y)
         (pa/ir q)))))
  '(((_.0 _.1) (pa/ir _.1))
    ((_.0 _.1) (=/= ((_.0 . _.1))) (pa/ir _.1))))

(mtest "occurs-check-0"
  (run* (q)
    (exist (x)
      (==-check q `(,x))
      (==-check x q)))
  '())

(mtest "non-tabled 0s fixed"
  (letrec
    ((f (lambda (x)
          (conde
            ((== x '()))
            ((exist (y)
               (== x `(0 . ,y))
               (f y)))))))
    (run* (q)
      (exist (a b)
        (== q `(,a ,b))
        (f q)
        (f b))))
  '())

(mtest "tabled 0s fixed"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x '()))
            ((exist (y)
               (== x `(0 . ,y))
               (f y)))))))
    (run* (q)
      (exist (a b)
        (== q `(,a ,b))
        (f q)
        (f b))))
  '())

(ftest "nest 3"
  (letrec
    ((nest (tabled (x)
             (conde
               ((== x '()))
               ((exist (y)
                  (== x `(,y))
                  (nest y)))))))
    (run+ (q) (nest q)))
  '(() (()) ((()))))

(ftest "listo"
  (letrec
    ((listo (tabled (ls)
              (conde
                ((== ls '()))
                ((exist (a d)
                   (== ls `(,a . ,d))
                   (listo d)))))))
    (run+ (q) (listo q)))
  '(() (_.0) (_.0 _.1) (_.0 _.1 _.2) (_.0 _.1 _.2 _.3) (_.0 _.1 _.2 _.3 _.4)))

(mtest "simple f"
  (let ((f (tabled (x y) (== x y))))
    (run* (q) (f 2 q)))
  '(2))

(mtest "simple f conde"
  (let ((f (tabled (x y) (conde
                           ((== x y))
                           ((== x #f))))))
    (run* (q) (f q #t)))
  '(#t #f))

(test "simple recursion"
  (letrec ((f (tabled (x)
                (conde
                  ((== x 0))
                  ((f x))))))
    (run 1 (q) (f q)))
  '(0))

(ftest "skipped recursion"
  (letrec ((g (tabled (x y)
                (conde ((== x y)) ((g x y))))))
    (run+ (q) (g 2 q)))
  '(2))

(mtest "no duplicates"
  (letrec ((g (tabled (x y)
                (conde ((g x y)) ((== x y))))))
    (run* (q) (g 2 q)))
  '(2))

(mtest "appendo gt 7 right order"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (== l `(,a . ,d))
                     (== out `(,a . ,res))
                     (appendo d s res)))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo gt 7" (skip "no true conjunction") ; DIVERGES - don't have true conjunction when there is sharing of variables between the conjuncts
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo non-tabled 7 nothing" (skip "no true conjunction") ; tabling isn't the only problem
  (letrec
    ((appendo (lambda (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo non-tabled 7 multi" (skip "no true conjunction")
  (letrec
    ((appendo (lambda (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (multi (l s out a d res)
                       (== l `(,a . ,d))
                       (appendo d s res)
                       (== out `(,a . ,res)))))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo gt 7 multi right order"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (multi (l s out a d res)
                       (== l `(,a . ,d))
                       (== out `(,a . ,res))
                       (appendo d s res))))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo gt 7 multi" (skip "no true conjunction")
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (multi (l s out a d res)
                       (== l `(,a . ,d))
                       (appendo d s res)
                       (== out `(,a . ,res)))))))))
    (run 7 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "multi tabled appendo 3"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (multi (l s out a d res)
                       (== l `(,a . ,d))
                       (== out `(,a . ,res))
                       (appendo d s res))))))))
    (run 3 (q)
      (exist (x y)
        (== q `(,x ,y))
        (appendo x y '(cake)))))
  '(((cake) ()) (() (cake))))

(mtest "multi prefix 2"
  (letrec
    ((f (tabled (l p)
          (conde
            ((== p '()))
            ((exist (a d r)
               (multi (a d r)
                 (== l `(,a . ,d))
                 (== p `(,a . ,r))
                 (f d r))))))))
    (run 2 (q) (f '() q)))
  '(()))

(mtest "non-multi prefix 3"
  (letrec
    ((f (tabled (l p)
          (conde
            ((== p '()))
            ((exist (a d r)
               (== l `(,a . ,d))
               (== p `(,a . ,r))
               (f d r)))))))
    (run 3 (q) (f '(cake) q)))
  '(() (cake)))

(mtest "multi prefix 3"
  (letrec
    ((f (tabled (l p)
          (conde
            ((== p '()))
            ((exist (a d r)
               (multi (a d r)
                 (== l `(,a . ,d))
                 (== p `(,a . ,r))
                 (f d r))))))))
    (run 3 (q) (f '(cake) q)))
  '(() (cake)))

(mtest "multi tabled appendo 4"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (multi (l s out a d res)
                       (== l `(,a . ,d))
                       (== out `(,a . ,res))
                       (appendo d s res))))))))
    (run 4 (q)
      (exist (x y)
        (== q `(,x ,y))
        (appendo x y '(cake with)))))
  '(((cake with) ()) ((cake) (with)) (() (cake with))))

(mtest "multi-tabled non-rec"
  (letrec
    ((h (tabled (x y)
          (conde
            ((== x y))
            ((exist (a) (== x `(,a . ,y)))))))
     (g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (h d y)
                 (== x `(,a . ,d)))))))))
    (run* (q) (g '(a b c) q)))
  '((a b c) (b c) (c)))

(mtest "multi-tabled1 small0" (skip "no true conjunction")
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q)
      (g '(a) q)))
  '((a) ()))

(mtest "multi-non-tabled1 small1" (skip "no true conjunction")
  (letrec
    ((g (lambda (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q) (g '(a b) q)))
  '((a b) (b) ()))

(mtest "multi-tabled1 small1 doublea" (skip "no true conjunction")
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q)
      (g '(a a) q)))
  '((a a) (a) ()))

(mtest "multi-tabled1 small1 right order"
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (== x `(,a . ,d))
                 (g d y))))))))
    (run* (q)
      (g '(a b) q)))
  '((a b) (b) ()))

(mtest "multi-tabled1 small1" (skip "no true conjunction")
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q)
      (g '(a b) q)))
  '((a b) (b) ()))

(mtest "multi mutual recursion tabled 1" (skip "no true conjunction")
  (letrec
    ((f (tabled (x y)
          (conde
            ((== x '()) (== y '()))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d))))))))
     (g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (f d y)
                 (== x `(,a . ,d)))))))))
    (run* (q) (f '(a a b) q)))
  '((a b) ()))

(mtest "multi-tabled1" (skip "no true conjunction")
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q)
      (g '(a b c d e) q)))
  '((a b c d e) (b c d e) (c d e) (d e) (e) ()))

#|
note: the second test is too difficult
this kind of loop shouldn't show up in practice
it can be avoided with tabling as long as the argument list doesn't change

(mtest "symconj0"
  (run* (q) (== #t #f) (let l () (exist () (l))))
  '())

(mtest "symconj1"
  (run* (q) (let l () (exist () (l))) (== #t #f))
  '())
|#

(mtest "comconj0" (skip "no true conjunction")
  (run* (q) (let l () (conde ((l)) ((l)))) (== #t #f))
  '())

(mtest "comconj1" (skip "no true conjunction")
  (run* (q) (let l () (conde ((l)) ((let l () (conde ((l)) ((l))))))) (== #t #f))
  '())

(mtest "comconj2" (skip "no true conjunction")
  (run* (q)
    (let l () (conde ((l)) ((l))))
    (let l () (conde ((l)) ((l))))
    (== #f #t))
  '())

(letrec
  ((one-step
     (lambda (n x)
       (conde
         [(== n x)]
         [(one-step (+ 1 n) x)]))))

  (ftest "multi1" ; note - doesn't check that we don't produce duplicates
    (run+ (q)
      (exist (x y)
        (multi (x y) (one-step 0 x) (one-step 10 y))
        (== `(,x ,y) q)))
    '((0 10) (0 11) (1 10) (0 12) (0 13) (2 10) (3 10)))

  (mtest "-multi2" (skip "no true conjunction")
    (run 5 (q)
      (exist (x y)
        (one-step 0 x)
        (one-step 10 y)
        (== #f #t)
        (== `(,x ,y) q)))
    '())

  (mtest "multi2" (skip "no true conjunction")
    (run 5 (q)
      (exist (x y)
        (multi () (multi (x y) (one-step 0 x) (one-step 10 y)) (== #f #t))
        (== `(,x ,y) q)))
    '())

  (mtest "multi3"
    (run 5 (q)
      (exist (x y)
        (multi () (== #f #t) (multi (x y) (one-step 0 x) (one-step 10 y)))
        (== `(,x ,y) q)))
    '())

  (mtest "multi4" (skip "no true conjunction")
    (run 5 (q)
      (exist (x y)
        (multi (x) (one-step 0 x) (multi (y) (one-step 10 y) (== #f #t) ))
        (== `(,x ,y) q)))
    '()))

(letrec
  ((alwayso
     (lambda (g)
       (conde
         (g)
         ((alwayso g)))))
   (will-failo
     (lambda ()
       (== #f #t))))
  (mtest "multi5" (skip "no true conjunction")
    (run 5 (q)
      (multi ()
        (alwayso (== #f #f))
        (will-failo)))
    '()))

(mtest "multi-dup0"
  (letrec ((g (tabled (x y) (multi (x y) (== x 5) (== y 6)))))
    (run* (q)
      (exist (x y)
        (== q `(,x ,y))
        (g x y))))
  '((5 6)))

(mtest "multi-dup1"
  (run* (q)
    (exist (x y)
      (multi (x y) (== x 5) (== y 6))
      (== q `(,x ,y))))
  '((5 6)))

(mtest "multi-dup2"
  (run* (q)
    (exist (x y)
      (multi (x y) (== x 5) (== y 6) (== q `(,x ,y)))))
  '((5 6)))

(ftest "multi-tabled0"
  (letrec
    ((g (tabled (x y)
          (conde
            ((== x '()) (== y '()))
            ((exist (z)
               (multi (x y z)
                 (== x `(1 . ,y))
                 (g y z))))))))
    (run+ (q)
      (exist (y)
        (g q y))))
  '(() (1) (1 1) (1 1 1) (1 1 1 1)))

(mtest "tails"
  (letrec
    ((g (lambda (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (== x `(,a . ,d))
               (g d y)))))))
    (run* (q)
      (g '(a b c d e) q)))
  '((a b c d e) (b c d e) (c d e) (d e) (e) ()))

(mtest "multi-tails" (skip "no true conjunction")
  (letrec
    ((g (lambda (x y)
          (conde
            ((== x y))
            ((exist (a d)
               (multi (x y a d)
                 (g d y)
                 (== x `(,a . ,d)))))))))
    (run* (q)
      (g '(a b c d e) q)))
  '((a b c d e) (b c d e) (c d e) (d e) (e) ()))

#|
(let ((check-run
        (lambda (con)
          (and (assertion-violation? con)
            (eq? (condition-who con) 'run)))))

  (vtest "run error 0" check-run
    (run -10 (q) (== q 5)))

  (vtest "run error 1" check-run
    (run 0 (q) (== q 5)))

  (vtest "run error 2" check-run
    (run 'hello (q) (== q 5))))
|#

(test 'm1
  (answer-set-equal? '() '())
  #t)

(test 'm2
  (answer-set-equal? '(a) '())
  #f)

(test 'm3
  (answer-set-equal? '() '(a))
  #f)

(test 'm4
  (answer-set-equal? '(a) '(a a))
  #f)

(test 'm5
  (answer-set-equal? '(a a) '(a))
  #f)

(test 'm6
  (answer-set-equal? '(a a) '(a a))
  #t)

(test 'm7
  (answer-set-equal? '(a b a) '(a b))
  #f)

(test 'm8
  (answer-set-equal? '(a b a) '(b a a))
  #t)

(test 'm9
  (answer-set-equal? '(a b) '(a b a))
  #f)

(test 'm10
  (answer-set-equal?
    '((c a) (a a) (a b) (a c) (b a) (b b) (b c))
    '((a c) (c a)))
  #f)

(test 'm11
  (answer-set-equal?
    '((a c) (b a) (c a))
    '((c a) (a c)))
  #f)

(mtest "serious call"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x 0))
            ((g x)))))
     (g (tabled (x)
          (conde
            ((== x 1))
            ((== x 2))))))
    (run* (q) (f q)))
  '(0 1 2))

(test "tabled definition"
  (letrec
    ((g (tabled (x y)
          (conde ((== x y))
            ((g x y))))))
    #t)
  #t)

(mtest "simple g"
  (letrec ((g (tabled (x y)
                (conde ((== x y)) ((g x y))))))
    (run 2 (q) (g 2 q)))
  '(2))

(ftest "mutual recursion"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x 0))
            ((g x)))))
     (g (tabled (x)
          (conde
            ((== x 1))
            ((f x))))))
    (run+ (q) (f q)))
  '(0 1))

(ftest "simple listo"
  (letrec
    ((listo (tabled (ls)
              (conde
                ((== ls '()))
                ((exist (a d)
                   (== ls `(,a . ,d))
                   (listo d)))))))
    (run+ (q) (listo q)))
  '(()))

(mtest "simple g 3"
  (letrec ((g (tabled (x y)
                (conde ((== x y)) ((g x y))))))
    (run 3 (q) (g 2 q)))
  '(2))

(mtest "Guo Gupta 2008 CLSS Example 1"
  (letrec
    ((r (tabled (x y)
          (conde
            ((exist (z) (r x z) (p z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))
            ((== `(,x ,y) `(b c)))))))
    (run* (x) (r 'a x)))
  '(a c b))

(mtest "Guo Gupta 2008 CLSS Example 1 Extra Tabling"
  (letrec
    ((r (tabled (x y)
          (conde
            ((exist (z) (r x z) (p z y)))
            ((p x y)))))
     (p (tabled (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))
            ((== `(,x ,y) `(b c)))))))
    (run* (x) (r 'a x)))
  '(a c b))

(mtest "Guo Gupta 2001 LNCS Example 3"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((exist (z)  (r x z) (r z y)))
            ((p x y) (q y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(a d)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (y)
          (conde ((== y 'b)) ((== y 'c))))))
    (run* (y) (r 'a y)))
  '(c b))

(mtest "Sagonas Swift Example"
  (letrec
    ((p (tabled (x y)
          (conde
            ((exist (z) (p x z) (e z y)))
            ((e x y) (q y)))))
     (e (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(a d)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b))
            ((== x 'c))))))
    (run* (z) (p 'a z)))
  '(b c))

(ftest "Fig 21 non-tabled run 10" ; search strategy dependent
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((exist (y) (p x y)))))))
    (run+ (q) (exist (x y) 
                (== q `(,x ,y))
                (p x y))))
  '((c a) (a a) (a b) (a c) (b a) (b b) (b c)))

(ftest "Sagonas Swift Fig 21 no tabling" ; search strategy dependent
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((exist (y) (p x y)))))))
    (run+ (q) (exist (x y) 
                (== q `(,x ,y))
                (p x y))))
  '((a c) (a a)))

(mtest 'a1
  (run 3 (q) (== q 5) (== q 5))
  '(5))

(mtest 'a2
  (run 5 (q) (conde ((== q 3) (== q 4)) ((== q 5))))
  '(5))

(mtest 'a3
  (run 5 (q) (conde ((== q 3) (== q 3)) ((== q 5))))
  '(3 5))

(mtest 'a4
  (run 10 (q)
    (conde ((== q 3)) ((== q q)))
    (conde ((== q 3)) ((== q 4))))
  '(3 3 4))

(ftest "Simplified^2 non-tabled Guo Gupta 2001 LNCS Example 3"
 (letrec
   ((r (lambda (x y)
         (conde
           ((exist (z) (r x z) (r z y)))
           ((== `(,x ,y) `(a b)))
           ((== `(,x ,y) `(b c)))))))
   (run+ (y) (r 'a y)))
 '(c b))

(mtest "Simplified^2 tabled Guo Gupta 2001 LNCS Example 3"
 (letrec
   ((r (tabled (x y)
         (conde
           ((exist (z) (r x z) (r z y)))
           ((== `(,x ,y) `(a b)))
           ((== `(,x ,y) `(b c)))))))
   (run* (y) (r 'a y)))
 '(c b))

(mtest "Fig 21 really simplified"
  (letrec
    ((r (lambda (x)
          (conde
            ((== x 'c))
            ((r x))))))
    (run 1 (q) (r q)))
  '(c))

(mtest "Fig 21 simplified tabled"
  (letrec
    ((q (tabled (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (tabled (x)
          (conde
            ((== x 'c))
            ((r x))))))
    (run* (p)
      (exist (x y)
        (== p `(,x ,y))
        (q x)
        (r y))))
  '((a c) (b c)))

(mtest "Simplified Guo Gupta 2001 LNCS Example 3"
  (letrec
    ((r (tabled (x y)
          (conde
            ((exist (z) (r x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run* (y) (r 'a y)))
  '(c b))

(ftest "Simplified non-tabled Guo Gupta 2001 LNCS Example 3"
  (letrec
    ((r (lambda (x y)
          (conde
            ((exist (z) (r x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run+ (y) (r 'a y)))
  '(c b))

(mtest "Guo Gupta 2001 LNCS Example 2"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((exist (z)
               (conde
                 ((r x z) (p z y))
                 ((r x z) (q z y)))))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (x y)
          (== `(,x ,y) `(c d)))))
    (run* (y) (r 'a y)))
  '(d c b))

(mtest "Guo Gupta 2001 LNCS Example 4"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((exist (z) (p x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))))))
    (run 10 (y) (r 'a y)))
  '(a b))

(mtest "Warren Figure 4"
  (letrec 
    ((path (tabled (x y)
             (conde
               ((arc x y))
               ((exist (z) (arc x z) (path z y))))))
     (arc (lambda (x y)
            (conde
              ((== `(,x ,y) `(a b)))
              ((== `(,x ,y) `(b a)))
              ((== `(,x ,y) `(b d)))))))
    (run* (a) (path 'a a)))
  '(b a d))

(mtest "Guo Gupta 2008 CLSS Example 4"
  (letrec
    ((r (tabled (x y)
          (conde
            ((exist (z)
               (conde
                 ((r x z) (q z y))
                 ((r x z) (p z y)))))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(c d))))))
     (q (lambda (x y)
          (== `(,x ,y) `(b c)))))
    (run* (y) (r 'a y)))
  '(d c b))

(mtest "Zhou Sato Example"
  (letrec
    ((p (tabled (x y)
          (conde
            ((exist (z) (p x z) (e z y)))
            ((e x y)))))
     (e (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run 10 (q) (p 'a q)))
  '(b c))

(mtest "Sagonas Swift Fig 12"
  (letrec
    ((a (tabled (x y)
          (conde
            ((c x y))
            ((exist (z)  (b x z) (c z y))))))
     (b (tabled (x y)
          (conde
            ((d x y))
            ((exist (z) (a x z) (c z y))))))
     (c (lambda (x y)
          (conde
            ((== `(,x ,y) '(0 1)))
            ((== `(,x ,y) `(1 2))))))
     (d (lambda (x y)
          (conde
            ((== `(,x ,y) '(0 1)))
            ((== `(,x ,y) `(1 2)))))))
    (run* (x) (a 0 x)))
  '(1 2))

(mtest "Sagonas Swift Fig 21 no tabling no recursion"
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (== x 'c))))
    (run 10 (q) (exist (x y)
                  (== q `(,x ,y))
                  (p x y))))
  '((a c) (b c) (c a)))

(ftest "Sagonas Swift Fig 21 no tabling simplified"
  (letrec
    ((p (lambda (x y) (exist () (q x) (r y))))
     (q (lambda (x) (== x 'a)))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((exist (y) (p x y)))))))
    (run+ (q) (exist (x y)
                 (== q `(,x ,y))
                 (p x y))))
  '((a c)))

(mtest "Sagonas Swift Fig 21"
  (letrec
    ((p (tabled (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (tabled (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (tabled (x)
          (conde
            ((== x 'c))
            ((exist (y) (p x y)))))))
    (run 10 (q) (exist (x y)
                    (== q `(,x ,y))
                    (p x y))))
  '((c a) (a a) (a b) (a c) (b a) (b b) (b c)))

(ftest "farmer no tabling"
  (letrec
    ((state
       (lambda (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (exist (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (lambda (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (lambda (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FC FG FW FF FG)))

(ftest "farmer tabled state only"
  (letrec
    ((state
       (tabled (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (exist (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (lambda (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (lambda (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FC FG FW FF FG)))

(ftest "farmer"
  (letrec
    ((state
       (tabled (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (exist (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (exist (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (tabled (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (tabled (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FW FG FC FF FG) (FG FF FC FG FW FF FG)))

(ftest "alternative farmer"
  (letrec
    ((valid
       (tabled (farmer wolf goat cabbage path)
         (safe farmer wolf goat cabbage)
         (conde
           ((== `(,farmer ,wolf ,goat ,cabbage) '(north north north north))
            (== path '()))
           ((exist (which new-farmer new-wolf new-goat new-cabbage new-path)
              (== path `(,which . ,new-path))
              (opposite farmer new-farmer)
              (one-with farmer new-farmer which
                `((FW ,wolf ,new-wolf)
                  (FG ,goat ,new-goat)
                  (FC ,cabbage ,new-cabbage)))
              (valid new-farmer new-wolf new-goat new-cabbage new-path))))))
     (one-with
       (tabled (oldf newf which choices)
         (conde
           ((== choices '()) (== which 'FF))
           ((exist (choice rest)
              (== choices `(,choice . ,rest))
              (conde
                ((== choice `(,which ,oldf ,newf)) (stay rest))
                ((stay `(,choice)) (one-with oldf newf which rest))))))))
     (stay
       (tabled (choices)
         (conde
           ((== choices '()))
           ((exist (tag pos rest)
              (== choices `((,tag ,pos ,pos) . ,rest))
              (stay rest))))))
     (opposite
       (tabled (pos1 pos2)
         (conde
           ((== pos1 'north) (== pos2 'south))
           ((== pos1 'south) (== pos2 'north)))))
     (safe
       (tabled (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (valid 'south 'south 'south 'south q)))
  '((FG FF FW FG FC FF FG) (FG FF FC FG FW FF FG)))

(mtest "fg1"
  (letrec
    ((f (tabled (x p)
          (conde
            ((== x 0) (== p '()))
            ((exist (q) (g x q) (== p `(1 . ,q)))))))
     (g (tabled (x q)
          (conde
            ((== x 1) (== q '()))
            ((f x q))))))
    (run 10 (q) (f 2 q)))
  '())

(mtest "fg2"
  (letrec
    ((f (tabled (x p)
          (exist (q)
            (conde
              ((== x 0) (== p `(z . ,q)))
              ((g x q) (== p `(g . ,q)))))))
     (g (tabled (x p)
          (exist (q)
            (conde
              ((== x 1) (== p `(o . ,q)))
              ((f x q) (== p `(f . ,q))))))))
    (run* (q) (f 2 q)))
  '())

(ftest "fg3"
  (letrec
    ((f (tabled (x p)
          (exist (q)
            (conde
              ((== x 0) (== p `(z . ,q)))
              ((g x q) (== p `(g . ,q)))))))
     (g (tabled (x p)
          (exist (q)
            (conde
              ((== x 1) (== p `(o . ,q)))
              ((f x q) (== p `(f . ,q))))))))
    (run+ (q) (f 1 q)))
  '((g o . _.0) (g f g o . _.0) (g f g f g o . _.0)))

(ftest "ab1"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((exist (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run+ (q)
      (exist (i o r)
        (== q `(,i ,o ,r))
        (b i o r))))
  '(((0 . _.0) _.0 z)))

(mtest "bobo0nt"
  (letrec
    ((b (lambda (i o)
          (conde
            ((== i `(0 . ,o)))
            ((exist (bo) (b i o) (b o bo)))))))
    (run 2 (q)
      (exist (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) (0 . _.0))))

(mtest "bobo1"
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((exist (bo) (b i o) (b o bo)))))))
    (run 2 (q)
      (exist (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)))

(mtest "bio0"
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((exist (bo) (b i bo) (b bo o)))))))
    (run 2 (q)
      (exist (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) _.0)))

(mtest "ab0"
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((exist (bo) (b i bo) (a bo o))))))
     (a (tabled (i o)
          (conde ((a i o)) ((b i o))))))
    (run 2 (q)
      (exist (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) _.0)))

(mtest "ab2"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((exist (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run 1 (q)
      (exist (i o r)
        (== q `(,i ,o ,r))
        (b i o r))))
  '(((0 . _.0) _.0 z)))

(mtest "ab3"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((exist (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run 1 (q)
      (exist (i o r _.0)
        (== q `(,i ,o ,r))
        (b i o r)
        (== q `((0 0 . ,_.0) (0 . ,_.0) z)))))
  '(((0 0 . _.0) (0 . _.0) z)))

(mtest "structural alwayso 2 non-tabled" ; succeeds with duplicates (see below)
  (letrec
    ((alwayso (lambda (x)
                (conde
                  ((== #f #f))
                  ((alwayso `(,x)))))))
    (run 2 (q)
      (alwayso q)))
  '(_.0 _.0))

(mtest "structural alwayso 1" ; NOTE run 2 diverges because there is only one answer and the changing structure defeats the tabling
  (letrec
    ((alwayso (tabled (x)
                (conde
                  ((== #f #f))
                  ((alwayso `(,x)))))))
    (run 1 (q)
      (alwayso q)))
  '(_.0))

(mtest "appendo gt 6"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((exist (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 6 (q)
      (exist (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "alwayso many answers"
  (letrec
    ((alwayso (tabled (x)
                (conde
                  ((== '() x))
                  ((exist (y)
                     (== `(,y) x)
                     (alwayso y)))))))
    (run 10 (q) (alwayso q)))
  '(() (()) ((())) (((()))) ((((())))) (((((())))))
    ((((((())))))) (((((((()))))))) ((((((((()))))))))
    (((((((((())))))))))))

(mtest "subsumption 1"
  (letrec
    ((r (tabled (a b o)
          (conde
            ((== a #t))
            ((== a #f))
            ((r b a o)))
          (== o `(,a ,b)))))
    (run* (z) (exist (x y) (r x y z))))
  '((#t _.0) (#f _.0)))

(mtest "subsumption 2"
  (letrec
    ((r (tabled (a b o)
          (== o `(,a ,b))
          (conde
            ((== a #t))
            ((== a #f))
            ((r b a o))))))
    (run* (z) (exist (x y) (r x y z))))
  '((#t _.0) (#f _.0)))

(ftest "radar"
  (let-syntax
    ((e-over-timesteps
       (lambda (o)
         (syntax-case o ()
           ((_ e-blips (x ...))
            (with-syntax 
              (((xa ...) (generate-temporaries #'(x ...)))
               ((xd ...) (generate-temporaries #'(x ...))))
              #'(lambda (x ...)
                  (let f ((x x) ...)
                    (conde
                      ((== x '()) ...)
                      ((exist (xa ... xd ...)
                         (== x `(,xa . ,xd)) ...
                         (e-blips xa ...)
                         (f xd ...))))))))))))
    (letrec
      ((e-random-position
         (lambda (v)
           (exist (x y) (== v `(,x ,y))
             (e-member x (range 0 maximum-coordinate))
             (e-member y (range 0 maximum-coordinate)))))
       (e-member
         (lambda (x ls)
           (exist (a d) (== ls `(,a . ,d))
             (conde ((== a x)) ((e-member x d))))))
       (range
         (case-lambda
           ((a b)
            (let f ((b (- b 1)) (r '()))
              (if (= b a) `(,a . ,r)
                (f (- b 1) `(,b . ,r)))))
           ((b) (range 1 b))))
       (maximum-coordinate 19)
       (e-observed-blips
         (lambda (ps gs os)
           (conde
             ((== gs '()) (== os '()))
             ((exist (id gd px py od)
                (== gs `(,id . ,gd))
                (== os `((,px ,py) . ,od))
                (conde
                  ((== id #f) (e-random-position `(,px ,py)))
                  ((project (id ps)
                     (cond
                       ((assv id ps)
                        => (lambda (p)
                             (let ((f (lambda (x px)
                                        (let ((g (lambda (s)
                                                   (conde
                                                     ((== px (s x 1)))
                                                     ((== px (s x 2)))))))
                                          (conde ((== px x)) ((g +)) ((g -)))))))
                               (exist () (f (cadr p) px) (f (caddr p) py)))))
                       (else (== #t #f))))))
                (e-observed-blips ps gd od))))))
       (e-observed-sequence (e-over-timesteps e-observed-blips (pt gt ot))))
      (run+ (q)
        (e-observed-sequence
          '(((0 0 0) (1 1 3) (2 2 3))
            ((0 3 3) (1 1 2) (2 5 3))
            ((0 6 6) (1 1 1) (2 8 3)))
          '((1 2) (0 1 2) (0 1 #f))
          q))))
  '((((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 1)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (1 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 2)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 2) (0 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 7) (1 1) (0 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 4)) ((6 6) (1 1) (0 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 3)))
    (((1 3) (2 4)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 0)))
    (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (1 1)))))

(mtest "testc11.tex-1" 
  (run* (q) (== #f #t))
  `())

(mtest "testc11.tex-2"   
  (run* (q)
    (== #t q))
  `(#t))

(mtest "testc11.tex-3"   
  (run* (q) 
    (== #f #t)
    (== #t q))
  `())

(mtest "testc11.tex-4"   
  (run* (q) 
    (== #t #t) 
    (== #t q))
  (list #t))

(mtest "testc11.tex-5"   
  (run* (q) 
    (== #t #t) 
    (== #t q))
  `(#t))

(mtest "testc11.tex-6"   
  (run* (r) 
    (== #t #t) 
    (== 'corn r))
  (list 'corn))

(mtest "testc11.tex-7"   
  (run* (r) 
    (== #t #t) 
    (== 'corn r))
  `(corn))

(mtest "testc11.tex-8"   
  (run* (r)
    (== #f #t)
    (== 'corn r))
  `())

(mtest "testc11.tex-9"   
  (run* (q) 
    (== #t #t) 
    (== #f q))
  `(#f))

(mtest "testc11.tex-10" 
  (run* (x)
    (let ((x #f))
      (== #t x)))
  '())

(mtest "testc11.tex-11" 
  (run* (q)
    (exist (x)
      (== #t x)
      (== #t q)))
  (list #t))

(mtest "testc11.tex-12" 
  (run* (q)
    (exist (x)
      (== x #t)
      (== #t q)))
  (list #t))

(mtest "testc11.tex-13" 
  (run* (q)
    (exist (x)
      (== x #t)
      (== q #t)))
  (list #t))

(mtest "testc11.tex-14"   
  (run* (x)
    (== #t #t))
  (list `_.0))

(mtest "testc11.tex-15"   
  (run* (x)
    (let ((x #f))
      (exist (x)
        (== #t x))))
  `(_.0))

(mtest "testc11.tex-16" 
  (run* (r)
    (exist (x y)
      (== (cons x (cons y '())) r)))
  (list `(_.0 _.1)))

(mtest "testc11.tex-17" 
  (run* (s)
    (exist (t u)
      (== (cons t (cons u '())) s)))
  (list `(_.0 _.1)))

(mtest "testc11.tex-18" 
  (run* (r)
    (exist (x)
      (let ((y x))
        (exist (x)
          (== (cons y (cons x (cons y '()))) r)))))
  (list `(_.0 _.1 _.0)))

(mtest "testc11.tex-19" 
  (run* (r)
    (exist (x)
      (let ((y x))
        (exist (x)
          (== (cons x (cons y (cons x '()))) r)))))
  (list `(_.0 _.1 _.0)))

(mtest "testc11.tex-20" 
  (run* (q) 
    (== #f q)
    (== #t q))
  `())

(mtest "testc11.tex-21"   
  (run* (q) 
    (== #f q)
    (== #f q))
  '(#f))

(mtest "testc11.tex-22" 
  (run* (q)
    (let ((x q))
      (== #t x)))
  (list #t))

(mtest "testc11.tex-23" 
  (run* (r)
    (exist (x)
      (== x r)))
  (list `_.0))

(mtest "testc11.tex-24" 
  (run* (q)
    (exist (x)
      (== #t x)
      (== x q)))
  (list #t))

(mtest "testc11.tex-25" 
  (run* (q)
    (exist (x)
      (== x q)
      (== #t x)))
  (list #t))

(mtest "testc11.tex-26" 
  (run* (q)
    (exist (x)
      (== (eq? x q) q)))
  (list #f))

(mtest "testc11.tex-27" 
  (run* (q)
    (let ((x q))
      (exist (q)
        (== (eq? x q) x))))
  (list #f))

(mtest "testc13.tex-fail1"
  (run* (q)
    (conde 
      ((== #t #f) (== #f #f)) 
      ((== #f #f) (== #t #f))))
  '())

(test "testc13.tex-succeed1"
  (not
    (null?
      (run* (q)
        (conde
          ((== #t #f) (== #t #f))
          ((== #t #t) (== #t #t))))))
  #t)
  
(test "testc13.tex-succeed2"
  (not
    (null?
      (run* (q)
        (conde
          ((== #t #t) (== #t #t))
          ((== #t #t) (== #t #f))))))
  #t)
  

(mtest "testc11.tex-30" 
  (run* (x)
    (conde
      ((== 'olive x) (== #t #t))
      ((== 'oil x) (== #t #t))))
  `(olive oil))

(ftest "testc11.tex-31" 
  (run+ (x)
    (conde
      ((== 'olive x) (== #t #t))
      ((== 'oil x) (== #t #t))))
  `(olive))

(mtest "testc11.tex-32" 
(run* (x)
  (conde
    ((== 'virgin x) (== #t #f))
    ((== 'olive x) (== #f #f))
    ((== #f #f) (== #f #f))
    ((== 'oil x) (== #f #f))))
`(olive _.0 oil))

(mtest "testc13.tex-conde1"
  (run* (x)
    (conde
      ((== 'olive x) (== #f #f))
      ((== #f #f) (== #f #f))
      ((== 'oil x) (== #f #f))))
  `(olive _.0 oil))
  
(ftest "testc11.tex-33" 
  (run+ (x)
    (conde
      ((== 'extra x) (== #f #f))
      ((== 'virgin x) (== #t #f))
      ((== 'olive x) (== #f #f))
      ((== 'oil x) (== #f #f))))
  `(extra olive))

(mtest "testc11.tex-34" 
  (run* (r)
    (exist (x y)
      (== 'split x)
      (== 'pea y)
      (== (cons x (cons y '())) r)))
  (list `(split pea)))

(mtest "testc11.tex-35" 
  (run* (r)
    (exist (x y)
      (conde
        ((== 'split x) (== 'pea y))
        ((== 'navy x) (== 'bean y)))
      (== (cons x (cons y '())) r)))
  `((split pea) (navy bean)))

(mtest "testc11.tex-36" 
  (run* (r)
    (exist (x y)
      (conde
        ((== 'split x) (== 'pea y))
        ((== 'navy x) (== 'bean y)))
      (== (cons x (cons y (cons 'soup '()))) r)))
  `((split pea soup) (navy bean soup)))

(letrec ((teacupo
        (lambda (x)
          (conde
            ((== 'tea x) (== #f #f))
            ((== 'cup x) (== #f #f))))))

  (mtest "testc23.tex-14"   
    (run* (r)
      (conde
        ((teacupo r) (== #f #f))
        ((== #f r) (== #f #f))))
    `(#f tea cup))

  (mtest "testc11.tex-37"   
    (run* (x)
      (teacupo x))
    `(tea cup))

  (mtest "testc11.tex-38"   
    (run* (r)
      (exist (x y)
        (conde
          ((teacupo x) (== #t y) (== #f #f))
          ((== #f x) (== #t y)))
        (== (cons x (cons y '())) r)))
    `((#f #t) (tea #t) (cup #t))))

(mtest "testc11.tex-39"   
  (run* (r)                                                                      
    (exist (x y z)                                                              
      (conde                                                                    
        ((== y x) (exist (x) (== z x)))                                         
        ((exist (x) (== y x)) (== z x)))                                        
      (== (cons y (cons z '())) r)))
  `((_.0 _.1) (_.0 _.1)))

(mtest "testc11.tex-40"
  (run* (r)                                                                      
    (exist (x y z)                                                              
      (conde                                                                    
        ((== y x) (exist (x) (== z x)))                                         
        ((exist (x) (== y x)) (== z x)))
      (== #f x)
      (== (cons y (cons z '())) r)))
  `((#f _.0) (_.0 #f)))

(mtest "testc11.tex-41" 
  (run* (q)
    (let ((a (== #t q))
          (b (== #f q)))
      b))
  '(#f))

(mtest "testc11.tex-42" 
  (run* (q)
    (let ((a (== #t q))
          (b (exist (x)
               (== x q)
               (== #f x)))
          (c (conde
               ((== #t q) (== #f #f))
               ((== #f #f) (== #f q)))))
      b))
  '(#f))

(mtest "testc12.tex-2" 
  (run* (r)
    (exist (y x)
      (== `(,x ,y) r)))
  (list `(_.0 _.1)))

(mtest "testc12.tex-3" 
  (run* (r)
    (exist (v w)
      (== (let ((x v) (y w)) `(,x ,y)) r)))
  `((_.0 _.1)))

(letrec ((caro (lambda (p a)
              (exist (d)
                (== (cons a d) p)))))

  (mtest "testc12.tex-6" 
    (run* (r)
      (caro `(a c o r n) r))
    (list 'a))

  (mtest "testc12.tex-8"   
    (run* (q) 
      (caro `(a c o r n) 'a)
      (== #t q))
    (list #t))

  (mtest "testc12.tex-10" 
    (run* (r)
      (exist (x y)
        (caro `(,r ,y) x)
        (== 'pear x)))
    (list 'pear))

  (mtest "testc12.tex-11"   
    (cons 
      (car `(grape raisin pear))
      (car `((a) (b) (c))))
    `(grape a))

  (mtest "testc12.tex-12" 
    (run* (r)
      (exist (x y)
        (caro `(grape raisin pear) x)
        (caro `((a) (b) (c)) y)
        (== (cons x y) r)))
    (list `(grape a)))

  (mtest "testc12.tex-13"   
    (cdr `(grape raisin pear))
    `(raisin pear))

(letrec ((cdro (lambda (p d)
              (exist (a)
                (== (cons a d) p)))))

  (mtest "testc12.tex-15" 
    (run* (r)
      (exist (v)
        (cdro `(a c o r n) v)
        (caro v r)))
    (list 'c))

  (mtest "testc12.tex-17" 
    (run* (r)
      (exist (x y)
        (cdro `(grape raisin pear) x)
        (caro `((a) (b) (c)) y)
        (== (cons x y) r)))
    (list `((raisin pear) a)))

  (mtest "testc12.tex-18"   
    (run* (q) 
      (cdro '(a c o r n) '(c o r n)) 
      (== #t q))
    (list #t))

  (mtest "testc12.tex-20" 
    (run* (x)
      (cdro '(c o r n) `(,x r n)))
    (list 'o))

  (mtest "testc12.tex-22" 
    (run* (l)
      (exist (x) 
        (cdro l '(c o r n))
        (caro l x)
        (== 'a x)))
    (list `(a c o r n)))

(letrec ((conso (lambda (a d p) (== (cons a d) p))))

  (mtest "testc12.tex-23" 
    (run* (l)
      (conso '(a b c) '(d e) l))
    (list `((a b c) d e)))

  (mtest "testc12.tex-24" 
    (run* (x)
      (conso x '(a b c) '(d a b c)))
    (list 'd))

  (mtest "testc12.tex-26" 
    (run* (r)
      (exist (x y z)
        (== `(e a d ,x) r)
        (conso y `(a ,z c) r)))
    (list `(e a d c)))

  (mtest "testc12.tex-27" 
    (run* (x)
      (conso x `(a ,x c) `(d a ,x c)))
    (list 'd))

  (mtest "testc12.tex-29" 
    (run* (l)
      (exist (x)
        (== `(d a ,x c) l)
        (conso x `(a ,x c) l)))
    (list `(d a d c)))

  (mtest "testc12.tex-30" 
    (run* (l)
      (exist (x)
        (conso x `(a ,x c) l)
        (== `(d a ,x c) l)))
    (list `(d a d c)))

  (mtest "testc12.tex-31" 
    (run* (l)
      (exist (d x y w s)
        (conso w '(a n s) s)
        (cdro l s)
        (caro l x)
        (== 'b x)
        (cdro l d)
        (caro d y)
        (== 'e y)))
    (list `(b e a n s)))

(letrec ((nullo (lambda (x) (== '() x))))

  (mtest "testc12.tex-34" 
    (run* (q)
      (nullo `(grape raisin pear))
      (== #t q))
    `())

  (mtest "testc12.tex-35" 
    (run* (q)
      (nullo '())
      (== #t q))
    `(#t))

  (mtest "testc12.tex-36"   
    (run* (x) 
      (nullo x))
    `(()))

(letrec ((eqo (lambda (x y) (== x y))))

  (mtest "testc12.tex-39" 
    (run* (q)
      (eqo 'pear 'plum)
      (== #t q))
    `())

  (mtest "testc12.tex-40" 
    (run* (q)
      (eqo 'plum 'plum)
      (== #t q))
    `(#t))

  (mtest "testc12.tex-46"   
    (run* (r) 
      (exist (x y)
        (== (cons x (cons y 'salad)) r)))
    (list `(_.0 _.1 . salad)))

(letrec ((pairo (lambda (p)
               (exist (a d)
                 (conso a d p)))))

  (mtest "testc12.tex-47" 
    (run* (q)
      (pairo (cons q q))
      (== #t q))
    `(#t))

  (mtest "testc12.tex-48" 
    (run* (q)
      (pairo '())
      (== #t q))
    `())

  (mtest "testc12.tex-49" 
    (run* (q)
      (pairo 'pair)
      (== #t q))
    `())

  (mtest "testc12.tex-50"   
    (run* (x) 
      (pairo x))
    (list `(_.0 . _.1)))

  (mtest "testc12.tex-51"   
    (run* (r) 
      (pairo (cons r 'pear)))
    (list `_.0))

(letrec
  ((listo
     (lambda (l)
       (conde
         ((nullo l) (== #f #f))
         ((pairo l)
          (exist (d)
            (cdro l d)
            (listo d)))))))

  (mtest "testc14.tex-5" 
    (run* (x)
      (listo `(a b ,x d)))
    (list `_.0))

(mtest "testc14.tex-6" 
  (run 1 (x)
    (listo `(a b c . ,x)))
  (list `()))


(dtest "testc14.tex-7"
  (run* (x)
    (listo `(a b c . ,x))))


(mtest "testc14.tex-8" 
  (run 5 (x)
    (listo `(a b c . ,x)))
  `(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)))

  (letrec
    ((lolo (lambda (l)
             (conde
               ((nullo l) (== #f #f))
               ((exist (a) 
                  (caro l a)
                  (listo a))
                (exist (d)
                  (cdro l d)
                  (lolo d)))))))

    (mtest "testc14.tex-9" 
      (run 1 (l)                                                                       
        (lolo l))                                                                     
      `(()))

    (mtest "testc14.tex-10" 
      (run* (q)
        (exist (x y) 
          (lolo `((a b) (,x c) (d ,y)))
          (== #t q)))
      (list #t))

    (mtest "testc14.tex-11" 
      (run 1 (q)
        (exist (x)
          (lolo `((a b) . ,x))
          (== #t q)))
      (list #t))

    (mtest "testc14.tex-12" 
      (run 1 (x)
        (lolo `((a b) (c d) . ,x)))
      `(()))

    (ftest "testc14.tex-13" 
      (run+ (x)
        (lolo `((a b) (c d) . ,x)))
      `(()
        (()) 
        ((_.0))
        (() ())
        ((_.0 _.1)))))

  (letrec ((twinso
          (lambda (s)
            (exist (x y)
              (conso x y s)
              (conso x '() y)))))

    (mtest "testc14.tex-14" 
      (run* (q)
        (twinso '(tofu tofu))
        (== #t q))

      (list #t))

    (mtest "testc14.tex-15" 
      (run* (z) 
        (twinso `(,z tofu)))
      (list `tofu))

    (letrec
      ((loto
         (lambda (l)
           (conde
             ((nullo l) (== #f #f))
             ((exist (a)
                (caro l a)
                (twinso a))
              (exist (d)
                (cdro l d)
                (loto d)))))))

      (mtest "testc14.tex-16" 
        (run 1 (z)
          (loto `((g g) . ,z)))
        (list `()))

      (mtest "testc14.tex-17" 
        (run 5 (z)
          (loto `((g g) . ,z)))
        '(()
          ((_.0 _.0))
          ((_.0 _.0) (_.1 _.1))
          ((_.0 _.0) (_.1 _.1) (_.2 _.2))
          ((_.0 _.0) (_.1 _.1) (_.2 _.2) (_.3 _.3))))

      (mtest "testc14.tex-18" 
        (run 5 (r)
          (exist (w x y z)
            (loto `((g g) (e ,w) (,x ,y) . ,z))
            (== `(,w (,x ,y) ,z) r)))
        '((e (_.0 _.0) ())
          (e (_.0 _.0) ((_.1 _.1)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2) (_.3 _.3)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2) (_.3 _.3) (_.4 _.4)))))

      (mtest "testc14.tex-19" 
        (run 3 (out)
          (exist (w x y z)
            (== `((g g) (e ,w) (,x ,y) . ,z) out)
            (loto out)))
        `(((g g) (e e) (_.0 _.0))
          ((g g) (e e) (_.0 _.0) (_.1 _.1))
          ((g g) (e e) (_.0 _.0) (_.1 _.1) (_.2 _.2)))))


    (letrec
      ((listofo
         (lambda (predo l)
           (conde
             ((nullo l) (== #f #f))
             ((exist (a)
                (caro l a)
                (predo a))
              (exist (d)
                (cdro l d)
                (listofo predo d)))))))

      (mtest "testc14.tex-20" 
        (run 3 (out)
          (exist (w x y z)
            (== `((g g) (e ,w) (,x ,y) . ,z) out)
            (listofo twinso out)))
        `(((g g) (e e) (_.0 _.0))
          ((g g) (e e) (_.0 _.0) (_.1 _.1))
          ((g g) (e e) (_.0 _.0) (_.1 _.1) (_.2 _.2)))))))

  (letrec
    ((membero
       (lambda (x l)
         (conde
           ((nullo l) (== #t #f))
           ((exist (a)
              (caro l a)
              (== a x))
            (== #f #f))
           ((== #f #f)
            (exist (d)
              (cdro l d)
              (membero x d)))))))

    (mtest "testc14.tex-22"   
      (run* (q) 
        (membero 'olive `(virgin olive oil))
        (== #t q))
      (list #t))

    (ptest "testc14.tex-23"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) `(hummus with pita))))
      (run 1 (y)
        (membero y `(hummus with pita))))

    (ptest "testc14.tex-24"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) '(with pita))))
      (run 1 (y) 
        (membero y `(with pita))))

    (mtest "testc14.tex-25"   
      (run 1 (y) 
        (membero y `(pita)))
      (list `pita))

    (mtest "testc14.tex-26"   
      (run* (y) 
        (membero y `()))
      `())

    (mtest "testc14.tex-27"   
      (run* (y) 
        (membero y `(hummus with pita)))
      `(hummus with pita))

    (mtest "testc14.tex-28"   
      (run* (x) 
        (membero 'e `(pasta ,x fagioli)))
      (list `e))

    (mtest "testc14.tex-29"   
      (run 1 (x) 
        (membero 'e `(pasta e ,x fagioli)))
      (list `_.0))

    (ptest "testc14.tex-30"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) '(e _.0))))
      (run 1 (x) 
        (membero 'e `(pasta ,x e fagioli))))

    (mtest "testc14.tex-31"   
      (run* (r)
        (exist (x y)
          (membero 'e `(pasta ,x fagioli ,y))
          (== `(,x ,y) r)))
      `((e _.0) (_.0 e)))

    (ftest "testc14.tex-32"   
      (run+ (l) (membero 'tofu l))
      `((tofu . _.0)))

    (dtest "testc14.tex-33"
      (run* (l) (membero 'tofu l)))

    (ftest "testc14.tex-34" 
      (run+ (l)
        (membero 'tofu l))
      `((tofu . _.0)
        (_.0 tofu . _.1)
        (_.0 _.1 tofu . _.2)
        (_.0 _.1 _.2 tofu . _.3)
        (_.0 _.1 _.2 _.3 tofu . _.4))))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x) (cdro l '()))
           ((exist (d)
              (cdro l d)
              (pmembero x d)))))))

    (ftest "testc14.tex-35"   
      (run+ (l)
        (pmembero 'tofu l))
      `((tofu)
        (_.0 tofu)
        (_.0 _.1 tofu)
        (_.0 _.1 _.2 tofu)
        (_.0 _.1 _.2 _.3 tofu)))

    (mtest "testc14.tex-36"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t)))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x)
            (conde
              ((cdro l '()))
              ((== #f #f))))
           ((exist (d)
              (cdro l d)
              (pmembero x d)))))))

    (mtest "testc14.tex-37"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t #t #t)))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x)
            (conde
              ((cdro l '()))
              ((exist (a d)
                 (cdro l `(,a . ,d))))))
           ((exist (d)
              (cdro l d)
              (pmembero x d)))))))

    (mtest "testc14.tex-38"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t #t))

    (ftest "testc14.tex-39" 
      (run+ (l)
        (pmembero 'tofu l))
      `((tofu)
        (tofu _.0 . _.1)
        (_.0 tofu)
        (_.0 tofu _.1 . _.2)
        (_.0 _.1 tofu)
        (_.0 _.1 tofu _.2 . _.3)
        (_.0 _.1 _.2 tofu)
        (_.0 _.1 _.2 tofu _.3 . _.4)
        (_.0 _.1 _.2 _.3 tofu)
        (_.0 _.1 _.2  _.3 tofu _.4 . _.5 )
        (_.0 _.1 _.2 _.3 _.4 tofu)
        (_.0 _.1 _.2 _.3 _.4 tofu _.5 . _.6))))

  (letrec
    ((memo
       (lambda (x l out)
         (conde
           ((caro l x) (== l out))
           ((exist (d)
              (cdro l d)
              (memo x d out)))))))

    (ftest "testc15.tex-7"   
      (run+ (out) 
        (memo 'tofu `(a b tofu d tofu e) out))
      `((tofu d tofu e)))

    (ftest "testc15.tex-8"   
      (run+ (out) 
        (exist (x)
          (memo 'tofu `(a b ,x d tofu e) out)))
      `((tofu d tofu e)))

    (mtest "testc15.tex-9"   
      (run* (r)
        (memo r
          `(a b tofu d tofu e)
          `(tofu d tofu e)))
      (list `tofu))

    (mtest "testc15.tex-10" 
      (run* (q)
        (memo 'tofu '(tofu e) '(tofu e))
        (== #t q))
      (list #t))

    (mtest "testc15.tex-11" 
      (run* (q)
        (memo 'tofu '(tofu e) '(tofu))
        (== #t q))
      `())

    (mtest "testc15.tex-12" 
      (run* (x)
        (memo 'tofu '(tofu e) `(,x e)))
      (list `tofu))

    (mtest "testc15.tex-13" 
      (run* (x)
        (memo 'tofu '(tofu e) `(peas ,x)))
      `())

    (mtest "testc15.tex-14"   
      (run* (out) 
        (exist (x) 
          (memo 'tofu `(a b ,x d tofu e) out)))
      `((tofu d tofu e) (tofu e)))

    (ftest "testc15.tex-15" 
      (run+ (z)
        (exist (u)
          (memo 'tofu `(a b tofu d tofu e . ,z) u)))
      `(_.0
         _.0
         (tofu . _.0)
         (_.0 tofu . _.1)
         (_.0 _.1 tofu . _.2)
         (_.0 _.1 _.2 tofu . _.3)
         (_.0 _.1 _.2 _.3 tofu . _.4)
         (_.0 _.1 _.2 _.3 _.4 tofu . _.5)
         (_.0 _.1 _.2 _.3 _.4 _.5 tofu . _.6)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 tofu . _.7)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 tofu . _.8)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 tofu . _.9))))

  (letrec
    ((rembero
       (lambda (x l out)
         (conde
           ((nullo l) (== '() out))
           ((caro l x) (cdro l out))
           ((exist (a d res)
              (conso a d l)
              (rembero x d res)
              (conso a res out)))))))

    (ftest "testc15.tex-17" 
      (run+ (out)
        (exist (y)
          (rembero 'peas `(a b ,y d peas e) out)))
      `((a b d peas e)))

    (mtest "testc15.tex-18" 
      (run* (out)
        (exist (y z)
          (rembero y `(a b ,y d ,z e) out)))
      `((b a d _.0 e)
        (a b d _.0 e)
        (a b d _.0 e)
        (a b d _.0 e)
        (a b _.0 d e)
        (a b e d _.0)
        (a b _.0 d _.1 e)))

    (mtest "testc15.tex-19" 
      (run* (r) 
        (exist (y z) 
          (rembero y `(,y d ,z e) `(,y d e))
          (== `(,y ,z) r)))
      `((d d)
        (d d)
        (_.0 _.0)
        (e e)))

    (ftest "testc15.tex-20" 
      (run+ (w)
        (exist (y z out)
          (rembero y `(a b ,y d ,z . ,w) out)))
      `(_.0 
         _.0
         _.0
         _.0
         _.0
         ()
         (_.0 . _.1)
         (_.0)
         (_.0 _.1 . _.2)
         (_.0 _.1)
         (_.0 _.1 _.2 . _.3)
         (_.0 _.1 _.2)
         (_.0 _.1 _.2 _.3 . _.4)))

    (let ((surpriseo
            (lambda (s)
              (rembero s '(a b c) '(a b c)))))

      (mtest "testc15.tex-21" 
        (run* (r)
          (== 'd r)
          (surpriseo r))
        (list 'd))

      (mtest "testc15.tex-22" 
        (run* (r)
          (surpriseo r))
        `(_.0))

      (mtest "testc15.tex-23" 
        (run* (r)
          (== 'b r)
          (surpriseo r))
        `(b))))

  (letrec
    ((appendo
       (lambda (l s out)
         (conde
           ((nullo l) (== s out))
           ((exist (a d res)
              (caro l a)
              (cdro l d)   
              (appendo d s res)
              (conso a res out)))))))

    (mtest "testc16.tex-5" 
      (run* (x)
        (appendo
          '(cake)
          '(tastes yummy)
          x))
      (list `(cake tastes yummy)))

    (mtest "testc16.tex-6" 
      (run* (x)
        (exist (y)
          (appendo
            `(cake with ice ,y)
            '(tastes yummy)
            x)))
      (list `(cake with ice _.0 tastes yummy)))

    (mtest "testc16.tex-7" 
      (run* (x)
        (exist (y)
          (appendo
            '(cake with ice cream)
            y
            x)))
      (list `(cake with ice cream . _.0)))

    (ftest "testc16.tex-8" 
      (run+ (x)
        (exist (y)
          (appendo `(cake with ice . ,y) '(d t) x)))
      (list `(cake with ice d t)))

    (ftest "testc16.tex-9" 
      (run+ (y)
        (exist (x)
          (appendo `(cake with ice . ,y) '(d t) x)))
      (list '())))

(letrec
  ((appendo
     (lambda (l s out)
       (conde
         ((nullo l) (== s out))
         ((exist (a d res)
            (conso a d l)
            (appendo d s res)
            (conso a res out)))))))

  (ftest "testc16.tex-10" 
    (run+ (x)
      (exist (y)
        (appendo `(cake with ice . ,y) '(d t) x)))
    `((cake with ice d t)
      (cake with ice _.0 d t)
      (cake with ice _.0 _.1 d t)
      (cake with ice _.0 _.1 _.2 d t)
      (cake with ice _.0 _.1 _.2 _.3 d t)))

  (ftest "testc16.tex-11" 
    (run+ (y)
      (exist (x)
        (appendo `(cake with ice . ,y) '(d t) x)))
    `(()
      (_.0)
      (_.0 _.1)
      (_.0 _.1 _.2)
      (_.0 _.1 _.2 _.3)))

  (ftest "testc16.tex-13" 
    (run+ (x)
      (exist (y)
        (appendo
          `(cake with ice . ,y)
          `(d t . ,y)
          x)))
    `((cake with ice d t)
      (cake with ice _.0 d t _.0)
      (cake with ice _.0 _.1 d t _.0 _.1)
      (cake with ice _.0 _.1 _.2 d t _.0 _.1 _.2)
      (cake with ice _.0 _.1 _.2 _.3 d t _.0 _.1 _.2 _.3)))

  (mtest "testc16.tex-14" 
    (run* (x)
      (exist (z)
        (appendo
          `(cake with ice cream)
          `(d t . ,z)
          x)))
    `((cake with ice cream d t . _.0)))

  (ftest "testc16.tex-15" 
    (run+ (x)
      (exist (y)
        (appendo x y `(cake with ice d t))))
    `(()
      (cake)
      (cake with)
      (cake with ice)
      (cake with ice d)
      (cake with ice d t)))

  (ftest "testc16.tex-16" 
    (run+ (y)
      (exist (x)
        (appendo x y `(cake with ice d t))))
    `((cake with ice d t)
      (with ice d t)
      (ice d t)
      (d t)
      (t)
      ()))

  (letrec ((appendxyquestion
        (lambda ()
          (run+ (r)
            (exist (x y)
              (appendo x y `(cake with ice d t))
              (== `(,x ,y) r)))))
      (appendxyanswer
        `((() (cake with ice d t))
          ((cake) (with ice d t))
          ((cake with) (ice d t))
          ((cake with ice) (d t))
          ((cake with ice d) (t))
          ((cake with ice d t) ()))))
  (ftest "appendxy"
    (appendxyquestion)
    appendxyanswer)

  (dtest "testc16.tex-17" ; (skip "conj stops divergence?")
    (run 7 (r)
      (exist (x y)
        (appendo x y `(cake with ice d t))
        (== `(,x ,y) r))))

  (letrec
    ((appendo
       (lambda (l s out)
         (conde
           ((nullo l) (== s out))
           ((exist (a d res)
              (conso a d l)
              (conso a res out)
              (appendo d s res)))))))

    (mtest "testc16.tex-18" 
      (run 7 (r)
        (exist (x y)
          (appendo x y `(cake with ice d t))
          (== `(,x ,y) r)))

      appendxyanswer)

    (ftest "testc16.tex-19" 
      (run+ (x)
        (exist (y z)
          (appendo x y z)))
      `(()
        (_.0)
        (_.0 _.1)
        (_.0 _.1 _.2)
        (_.0 _.1 _.2 _.3)
        (_.0 _.1 _.2 _.3 _.4)
        (_.0 _.1 _.2 _.3 _.4 _.5)))

    (ftest "testc16.tex-20" 
      (run+ (y)
        (exist (x z)
          (appendo x y z)))
      `(_.0 _.0 _.0 _.0 _.0 _.0  _.0))

    (ftest "testc16.tex-21" 
      (run+ (z)
        (exist (x y)
          (appendo x y z)))
      `(_.0
         (_.0 . _.1)
         (_.0 _.1 . _.2)
         (_.0 _.1 _.2 . _.3)
         (_.0 _.1 _.2 _.3 . _.4)
         (_.0 _.1 _.2 _.3 _.4 . _.5)
         (_.0 _.1 _.2 _.3 _.4 _.5 . _.6)))

    (ftest "testc16.tex-22" 
      (run+ (r)
        (exist (x y z)
          (appendo x y z)
          (== `(,x ,y ,z) r)))
      `((() _.0 _.0)
        ((_.0) _.1 (_.0 . _.1))
        ((_.0 _.1) _.2 (_.0 _.1 . _.2))
        ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
        ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))
        ((_.0 _.1 _.2 _.3 _.4) _.5 (_.0 _.1 _.2 _.3 _.4 . _.5))
        ((_.0 _.1 _.2 _.3 _.4 _.5) _.6 (_.0 _.1 _.2 _.3 _.4 _.5 . _.6))))))

  (letrec
    ((flatteno
       (lambda (s out)
         (conde
           ((nullo s) (== '() out))
           ((pairo s)
            (exist (a d res-a res-d)
              (conso a d s)
              (flatteno a res-a)
              (flatteno d res-d)
              (appendo res-a res-d out)))
           ((conso s '() out))))))

    (ftest "testc16.tex-33" 
      (run+ (x)
        (flatteno '((a b) c) x))
      `((((a b) c))
        ((a b) (c))
        ((a b) c)
        (a (b) (c))
        ((a b) c ())
        (a (b) c)
        (a (b) c ())
        (a b (c))
        (a b () (c))
        (a b c)))

    (ftest "testc16.tex-34" 
      (run+ (x)
        (flatteno '(a (b c)) x))
      `(((a (b c)))
        (a ((b c)))
        (a (b c))
        (a (b c) ())
        (a b (c))
        (a b (c) ())
        (a b c)
        (a b c ())
        (a b c ())
        (a b c () ())))

    (mtest "testc16.tex-35" 
      (run* (x)
        (flatteno '(a) x))
      `(((a))
        (a)
        (a ())))

    (mtest "testc16.tex-36" 
      (run* (x)
        (flatteno '((a)) x))
      `((((a)))
        ((a))
        ((a) ())
        (a)
        (a ())
        (a ())
        (a () ())))

    (mtest "testc16.tex-37" 
      (run* (x)
        (flatteno '(((a))) x))
      `(((((a))))
        (((a)))
        (((a)) ())
        ((a))
        ((a) ())
        ((a) ())
        ((a) () ())
        (a)
        (a ())
        (a ())
        (a () ())
        (a ())
        (a () ())
        (a () ())
        (a () () ())))
    
    (letrec ((flattenogrumblequestion
            (lambda ()
              (run* (x)
                (flatteno '((a b) c) x))))
          (flattenogrumbleanswer
            `((((a b) c))
              ((a b) (c))
              ((a b) c)
              (a (b) (c))
              ((a b) c ())
              (a (b) c)
              (a (b) c ())
              (a b (c))
              (a b () (c))
              (a b c)
              (a b c ())
              (a b () c)
              (a b () c ()))))

      (mtest "flattenogrumble"
        (flattenogrumblequestion)
        flattenogrumbleanswer)

      (dtest "testc16.tex-38"
        (run* (x)
          (flatteno x '(a b c)))))
    
    (test "testc16.tex-39" 
      (length
        (run* (x)
          (flatteno '((((a (((b))) c))) d) x)))
      574)))

  (letrec
    ((swappendo
       (lambda (l s out)
         (conde
           ((exist (a d res)
              (conso a d l)
              (conso a res out)
              (swappendo d s res)))
           ((nullo l) (== s out))))))

    (ftest "testc16.tex-23" 
      (run+ (r)
        (exist (x y z)
          (swappendo x y z)
          (== `(,x ,y ,z) r)))
      `((() _.0 _.0)
        ((_.0) _.1 (_.0 . _.1))
        ((_.0 _.1) _.2 (_.0 _.1 . _.2))
        ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
        ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))
        ((_.0 _.1 _.2 _.3 _.4) _.5 (_.0 _.1 _.2 _.3 _.4 . _.5))
        ((_.0 _.1 _.2 _.3 _.4 _.5) _.6 (_.0 _.1 _.2 _.3 _.4 _.5 . _.6)))))

  (letrec
    ((unwrapo
       (lambda (x out)
         (conde
           ((pairo x)
            (exist (a)
              (caro x a)
              (unwrapo a out)))
           ((== x out))))))

    (mtest "testc16.tex-26" 
      (run* (x)
        (unwrapo '(((pizza))) x))
      `((((pizza)))
        ((pizza))
        (pizza)
        pizza))

    (ftest "testc16.tex-27" 
      (run+ (x)
        (unwrapo x 'pizza))
      `(pizza))

    (ftest "testc16.tex-28" 
      (run+ (x)
        (unwrapo `((,x)) 'pizza))
      `(pizza))

    (ftest "testc16.tex-29" 
      (run+ (x)
        (unwrapo x 'pizza))
      `(pizza
         (pizza . _.0)
         ((pizza . _.0) . _.1)
         (((pizza . _.0) . _.1) . _.2)
         ((((pizza . _.0) . _.1) . _.2) . _.3)))

    (ftest "testc16.tex-30" 
      (run+ (x)
        (unwrapo x '((pizza))))
      `(((pizza))
        (((pizza)) . _.0)
        ((((pizza)) . _.0) . _.1)
        (((((pizza)) . _.0) . _.1) . _.2)
        ((((((pizza)) . _.0) . _.1) . _.2) . _.3)))

    (ftest "testc16.tex-31" 
      (run+ (x)
        (unwrapo `((,x)) 'pizza))
      `(pizza
         (pizza . _.0)
         ((pizza . _.0) . _.1)
         (((pizza . _.0) . _.1) . _.2)
         ((((pizza . _.0) . _.1) . _.2) . _.3))))

  (letrec ((strangeo (exist () strangeo)))
    (dtest "testc17.tex-1"
      (run 1 (x) strangeo))

    (ftest "testc17.tex-2" 
      (run+ (q)
        (conde
          (strangeo)
          ((== #f #f))))
      `(_.0)))

  (letrec ((strangero
             (conde 
               (strangero (conde 
                            (strangero) 
                            ((== #f #f))))
               ((== #f #f)))))

    (ftest "testc17.tex-3" 
      (run+ (q) 
        strangero)
      `(_.0 _.0 _.0 _.0 _.0)))

  (letrec
    ((strangesto
       (lambda (x y)
         (conde
           ((strangesto y x) (== #f y))
           ((== #f x))))))

    (ftest "testc17.tex-4" 
      (run+ (q)
        (exist (x y)
          (strangesto x y)
          (== `(,x ,y) q)))
      `((#f _.0) (_.0 #f) (#f #f) (#f #f) (#f #f))))

  (letrec
    ((any* (lambda (g) (conde (g) ((any* g))))))
    (let ((never (any* (== #t #f)))
          (always (any* (== #f #f))))

      (dtest "testc17.tex-5" 
        (run 1 (q)
          never 
          (== #t q)))

      (ftest "testc17.tex-6"   
        (run+ (q) 
          always 
          (== #t q))
        (list #t))

      (dtest "testc17.tex-7"
        (run* (q) 
          always 
          (== #t q)))

      (test "testc17.tex-8"   
        (run 5 (q) 
          always 
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-9"   
        (run 5 (q) 
          (== #t q) 
          always)
        `(#t #t #t #t #t))

      (letrec ((salo
              (lambda (g)
                (conde
                  ((== #f #f))
                  (g)))))

        (ftest "testc17.tex-10"   
          (run+ (q)
            (salo always)
            (== #t q))
          `(#t))

        (ftest "testc17.tex-11" 
          (run+ (q)
            (salo never)
            (== #t q))
          `(#t))

        (dtest "testc17.tex-12"
          (run* (q)
            (salo never)
            (== #t q)))

        (dtest "testc17.tex-13" ; (skip "conj stops divergence?")
          (run 1 (q)
            (salo never)
            (== #t #f)
            (== #t q)))

        (dtest "testc17.tex-14" ; (skip "conj stops divergence?")
          (run 1 (q) 
            always 
            (== #t #f)
            (== #t q))))

      (ftest "testc17.tex-15"   
        (run+ (q)
          (conde
            ((== #f q) always)
            ((== #t q)))
          (== #t q))
        `(#t))

      (dtest "testc17.tex-16" ; (skip "conj stops divergence?")
        (run 2 (q)
          (conde
            ((== #f q) always)
            ((== #t q)))
          (== #t q)))

      (test "testc17.tex-17"   
        (run 5 (q)
          (conde                                                                  
            ((== #f q) always)                                              
            ((any* (== #t q)))) 
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-18" 
        (run 5 (q)
          (conde
            (always)
            (never))
          (== #t q))
        `(#t #t #t #t #t))

      (ftest "testc17.tex-19"   
        (run+ (q)                                                                  
          (exist ()                                                                    
            (conde
              ((== #f q))
              ((== #t q)))                    
            always)                                                        
          (== #t q))
        `(#t))

      (test "testc17.tex-20"   
        (run 5 (q)
          (exist ()
            (conde
              ((== #f q))
              ((== #t q)))                    
            always)                                                        
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-21"   
        (run 5 (q)
          (exist ()
            (conde
              ((== #t q))
              ((== #f q)))
            always)                                           
          (== #t q))
        `(#t #t #t #t #t))))
  (letrec
    ((bit-xoro
       (lambda (x y r)
         (conde
           ((== 0 x) (== 0 y) (== 0 r))
           ((== 0 x) (== 1 y) (== 1 r))
           ((== 1 x) (== 0 y) (== 1 r))
           ((== 1 x) (== 1 y) (== 0 r)))))
     (bit-ando
       (lambda (x y r)
         (conde
           ((== 0 x) (== 0 y) (== 0 r))
           ((== 1 x) (== 0 y) (== 0 r))
           ((== 0 x) (== 1 y) (== 0 r))
           ((== 1 x) (== 1 y) (== 1 r))))))

    (mtest "testc20.tex-1" 
      (run* (s)
        (exist (x y)
          (bit-xoro x y 0)
          (== `(,x ,y) s)))  
      `((0 0)
        (1 1)))

    (mtest "testc20.tex-2" 
      (run* (s)
        (exist (x y)
          (bit-xoro x y 1)
          (== `(,x ,y) s)))
      `((0 1)
        (1 0)))

    (mtest "testc20.tex-3" 
      (run* (s)
        (exist (x y r)
          (bit-xoro x y r)
          (== `(,x ,y ,r) s)))
      `((0 0 0) 
        (0 1 1)
        (1 0 1)
        (1 1 0)))
    
  (mtest "testc20.tex-4" 
    (run* (s)
      (exist (x y)
        (bit-ando x y 1)
        (== `(,x ,y) s)))  
    `((1 1)))

    (letrec
      ((half-addero
         (lambda (x y r c)
           (exist ()
             (bit-xoro x y r)
             (bit-ando x y c)))))

      (mtest "testc20.tex-5" 
        (run* (r)
          (half-addero 1 1 r 1))
        (list 0))

      (mtest "testc20.tex-6" 
        (run* (s)
          (exist (x y r c)
            (half-addero x y r c)
            (== `(,x ,y ,r ,c) s)))
        `((0 0 0 0)
          (0 1 1 0)
          (1 0 1 0)
          (1 1 0 1)))

      (letrec
        ((full-addero
           (lambda (b x y r c)
             (exist (w xy wz)
               (half-addero x y w xy)
               (half-addero w b r wz)
               (bit-xoro xy wz c)))))

        (mtest "testc20.tex-7" 
          (run* (s)
            (exist (r c)
              (full-addero 0 1 1 r c)
              (== `(,r ,c) s)))
          (list `(0 1))))))

  (letrec
    ((full-addero
       (lambda (b x y r c)
         (conde
           ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
           ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
           ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
           ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
           ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
           ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
           ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
           ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))))

    (mtest "testc20.tex-8" 
      (run* (s)
        (exist (r c)
          (full-addero 1 1 1 r c)
          (== `(,r ,c) s)))
      (list `(1 1)))

    (mtest "testc20.tex-9" 
      (run* (s)
        (exist (b x y r c)
          (full-addero b x y r c)
          (== `(,b ,x ,y ,r ,c) s)))
      `((0 0 0 0 0)
        (1 0 0 1 0)
        (0 1 0 1 0)
        (1 1 0 0 1)
        (0 0 1 1 0)
        (1 0 1 0 1)
        (0 1 1 0 1)
        (1 1 1 1 1)))
    
(letrec
  ((poso
     (lambda (n)
       (exist (a d)
         (== `(,a . ,d) n)))))

  (mtest "testc20.tex-15" 
    (run* (q)
      (poso '(0 1 1))
      (== #t q))
    (list #t))

  (mtest "testc20.tex-16" 
    (run* (q)
      (poso '(1))
      (== #t q))
    (list #t))

  (mtest "testc20.tex-17" 
    (run* (q)
      (poso '())
      (== #t q))
    `())

  (mtest "testc20.tex-18" 
    (run* (r)
      (poso r))
    (list `(_.0 . _.1)))
  
  (letrec ((>1o
          (lambda (n)
            (exist (a ad dd)
              (== `(,a ,ad . ,dd) n)))))

    (mtest "testc20.tex-19" 
      (run* (q)
        (>1o '(0 1 1))
        (== #t q))
      (list #t))

    (mtest "testc20.tex-20" 
      (run* (q)
        (>1o '(0 1))
        (== #t q))
      `(#t))

    (mtest "testc20.tex-21" 
      (run* (q)
        (>1o '(1))
        (== #t q))
      `())

    (mtest "testc20.tex-22" 
      (run* (q)
        (>1o '())
        (== #t q))
      `())

    (mtest "testc20.tex-23" 
      (run* (r)
        (>1o r))
      (list 
        `(_.0 _.1 . _.2)))
    
    (letrec
      ((addero
         (lambda (d n m r)
           (conde
             ((== 0 d) (== '() m) (== n r))
             ((== 0 d) (== '() n) (== m r)
              (poso m))
             ((== 1 d) (== '() m)
              (addero 0 n '(1) r))
             ((== 1 d) (== '() n) (poso m)
              (addero 0 '(1) m r))
             ((== '(1) n) (== '(1) m)
              (exist (a c)
                (== `(,a ,c) r)
                (full-addero d 1 1 a c)))
             ((== '(1) n) (gen-addero d n m r))
             ((== '(1) m) (>1o n) (>1o r)
              (addero d '(1) n r))
             ((>1o n) (gen-addero d n m r)))))

       (gen-addero
         (lambda (d n m r)
           (exist (a b c e x y z)
             (== `(,a . ,x) n)
             (== `(,b . ,y) m) (poso y)
             (== `(,c . ,z) r) (poso z)
             (full-addero d a b c e)
             (addero e x y z)))))

      (ftest "testc20.tex-24" 
        (run+ (s)
          (exist (x y r)
            (addero 0 x y r)
            (== `(,x ,y ,r) s)))
        `((_.0 () _.0)
          (() (_.0 . _.1) (_.0 . _.1))
          ((1) (1) (0 1))))

      (ftest "testc20.tex-25"
        (run+ (s)
          (exist (x y r)
            (addero 0 x y r)
            (== `(,x ,y ,r) s)))
        `((_.0 () _.0)
          (() (_.0 . _.1) (_.0 . _.1))
          ((1) (1) (0 1))
          ((1) (0 _.0 . _.1) (1 _.0 . _.1))
          ((1) (1 1) (0 0 1))
          ((0 _.0 . _.1) (1) (1 _.0 . _.1))
          ((1) (1 0 _.0 . _.1) (0 1 _.0 . _.1))
          ((0 1) (0 1) (0 0 1))
          ((1) (1 1 1) (0 0 0 1))
          ((1 1) (1) (0 0 1))
          ((1) (1 1 0 _.0 . _.1) (0 0 1 _.0 . _.1))
          ((1 1) (0 1) (1 0 1))
          ((1) (1 1 1 1) (0 0 0 0 1))
          ((1 0 _.0 . _.1) (1) (0 1 _.0 . _.1))
          ((1) (1 1 1 0 _.0 . _.1) (0 0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1) (0 0 0 0 0 1))
          ((1 1 1) (1) (0 0 0 1))
          ((1) (1 1 1 1 0 _.0 . _.1) (0 0 0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1 1) (0 0 0 0 0 0 1))
          ((0 1) (1 1) (1 0 1))
          ((1 1 0 _.0 . _.1) (1) (0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1 0 _.0 . _.1) (0 0 0 0 0 1 _.0 . _.1))))

      (mtest "testc20.tex-26" 
        (run* (s)
          (gen-addero 1 '(0 1 1) '(1 1) s))
        (list `(0 1 0 1)))

      (mtest "testc20.tex-27" 
        (run* (s)
          (exist (x y)
            (addero 0 x y '(1 0 1))
            (== `(,x ,y) s)))
        `(((1 0 1) ())
          (() (1 0 1))
          ((1) (0 0 1))
          ((0 0 1) (1))
          ((1 1) (0 1))
          ((0 1) (1 1))))

      (let ((pluso (lambda (n m k) (addero 0 n m k))))
        (mtest "testc20.tex-28" 
          (run* (s)
            (exist (x y)
              (pluso x y '(1 0 1))
              (== `(,x ,y) s)))
          `(((1 0 1) ())
            (() (1 0 1))
            ((1) (0 0 1))
            ((0 0 1) (1))
            ((1 1) (0 1))
            ((0 1) (1 1))))

        (let ((minuso (lambda (n m k) (pluso m k n))))
          (letrec ((bumpo
                     (lambda (n x)
                       (conde
                         ((== n x) (== #f #f))
                         ((exist (m)
                            (minuso n '(1) m)
                            (bumpo m x)))))))
            (mtest "testc23.tex-18" 
              (run* (x)
                (bumpo '(1 1 1) x))
              `((1 1 1)
                (0 1 1)
                (1 0 1)
                (0 0 1)
                (1 1)
                (0 1)
                (1)
                ())))

          (mtest "testc20.tex-29" 
            (run* (q)
              (minuso '(0 0 0 1) '(1 0 1) q))
            `((1 1)))

          (mtest "testc20.tex-30" 
            (run* (q)
              (minuso '(0 1 1) '(0 1 1) q))
            `(()))

          (mtest "testc20.tex-31" 
            (run* (q)
              (minuso '(0 1 1) '(0 0 0 1) q))
            `())
          
          (letrec
            ((*o (lambda (n m p)
                   (conde
                     ((== '() n) (== '() p))
                     ((poso n) (== '() m) (== '() p))  
                     ((== '(1) n) (poso m) (== m p))   
                     ((>1o n) (== '(1) m) (== n p))
                     ((exist (x z)
                        (== `(0 . ,x) n) (poso x)
                        (== `(0 . ,z) p) (poso z)
                        (>1o m)
                        (*o x m z)))
                     ((exist (x y)
                        (== `(1 . ,x) n) (poso x)
                        (== `(0 . ,y) m) (poso y)
                        (*o m n p)))
                     ((exist (x y)
                        (== `(1 . ,x) n) (poso x)      
                        (== `(1 . ,y) m) (poso y)
                        (odd-*o x n m p))))))

             (odd-*o
               (lambda (x n m p)
                 (exist (q)
                   (bound-*o q p n m)
                   (*o x m q)
                   (pluso `(0 . ,q) m p))))

             (bound-*o
               (lambda (q p n m)
                 (== #f #f))))

            (dtest "testc21.tex-4"
              (run 2 (t)
                (exist (n m)
                  (*o n m '(1))
                  (== `(,n ,m) t)))))

          (letrec
            ((*o
               (lambda (n m p)
                 (conde
                   ((== '() n) (== '() p))
                   ((poso n) (== '() m) (== '() p))  
                   ((== '(1) n) (poso m) (== m p))   
                   ((>1o n) (== '(1) m) (== n p))
                   ((exist (x z)
                      (== `(0 . ,x) n) (poso x)
                      (== `(0 . ,z) p) (poso z)
                      (>1o m)
                      (*o x m z)))
                   ((exist (x y)
                      (== `(1 . ,x) n) (poso x)
                      (== `(0 . ,y) m) (poso y)
                      (*o m n p)))
                   ((exist (x y)
                      (== `(1 . ,x) n) (poso x)      
                      (== `(1 . ,y) m) (poso y)
                      (odd-*o x n m p))))))

             (odd-*o
               (lambda (x n m p)
                 (exist (q)
                   (bound-*o q p n m)
                   (*o x m q)
                   (pluso `(0 . ,q) m p))))

             (bound-*o
               (lambda (q p n m)
                 (conde
                   ((nullo q) (pairo p))
                   ((exist (x y z)
                      (cdro q x)
                      (cdro p y)
                      (conde
                        ((nullo n)
                         (cdro m z)
                         (bound-*o x y z '()))
                        ((cdro n z) 
                         (bound-*o x y z m)))))))))


            (ftest "testc21.tex-1" 
              (run+ (t)
                (exist (x y r)
                  (*o x y r)
                  (== `(,x ,y ,r) t)))
              `((() _.0 ())
                ((_.0 . _.1) () ())
                ((1) (_.0 . _.1) (_.0 . _.1))
                ((_.0 _.1 . _.2) (1) (_.0 _.1 . _.2))
                ((0 1) (_.0 _.1 . _.2) (0 _.0 _.1 . _.2))
                ((0 0 1) (_.0 _.1 . _.2) (0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 1) (0 1 _.0 . _.1))
                ((0 0 0 1) (_.0 _.1 . _.2) (0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 1) (0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 1) (0 0 1 _.0 . _.1))
                ((0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 1) (0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 1) (0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 1) (0 0 0 1 _.0 . _.1))
                ((1 1) (1 1) (1 0 0 1))
                ((0 0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 0 0 1 _.0 . _.1) (0 1) (0 0 0 0 1 _.0 . _.1))
                ((1 1) (1 0 1) (1 1 1 1))
                ((0 1 1) (1 1) (0 1 0 0 1))
                ((1 1) (1 1 1) (1 0 1 0 1))
                ((1 1) (0 1 1) (0 1 0 0 1))
                ((0 0 0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 0 0 1 _.0 . _.1) (0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((1 0 1) (1 1) (1 1 1 1))
                ((0 0 0 0 1 _.0 . _.1) (0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 1 1) (1 0 1) (0 1 1 1 1))
                ((0 0 1 1) (1 1) (0 0 1 0 0 1))
                ((1 1) (1 0 0 1) (1 1 0 1 1))))

            (mtest "testc21.tex-2" 
              (run* (p)
                (*o '(0 1) '(0 0 1) p))  
              (list `(0 0 0 1)))

            (ftest "testc21.tex-3" 
              (run+ (t)
                (exist (n m)
                  (*o n m '(1))
                  (== `(,n ,m) t)))
              (list `((1) (1))))
            
            (mtest "testc21.tex-6" ;(skip "*o looping")
              (run* (p)
                (*o '(1 1 1) '(1 1 1 1 1 1) p))
              (list `(1 0 0 1 1 1 0 1 1)))

            (letrec
              ((=lo
                 (lambda (n m)
                   (conde
                     ((== '() n) (== '() m))
                     ((== '(1) n) (== '(1) m))
                     ((exist (a x b y)
                        (== `(,a . ,x) n) (poso x)
                        (== `(,b . ,y) m) (poso y)
                        (=lo x y)))))))

              (mtest "testc21.tex-7" 
                (run* (t)
                  (exist (w x y)
                    (=lo `(1 ,w ,x . ,y) '(0 1 1 0 1))
                    (== `(,w ,x ,y) t)))
                (list `(_.0 _.1 (_.2 1))))

              (mtest "testc21.tex-8" 
                (run* (b)
                  (=lo '(1) `(,b)))
                (list 1))

              (mtest "testc21.tex-9" 
                (run* (n)
                  (=lo `(1 0 1 . ,n) '(0 1 1 0 1)))
                (list `(_.0 1)))

              (ftest "testc21.tex-10" 
                (run+ (t)
                  (exist (y z)
                    (=lo `(1 . ,y) `(1 . ,z))
                    (== `(,y ,z) t)))
                `((() ())
                  ((1) (1))
                  ((_.0 1) (_.1 1))
                  ((_.0 _.1 1) (_.2 _.3 1))
                  ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))))

              (ftest "testc21.tex-11" 
                (run+ (t)
                  (exist (y z)
                    (=lo `(1 . ,y) `(0 . ,z))
                    (== `(,y ,z) t)))
                `(((1) (1))
                  ((_.0 1) (_.1 1))
                  ((_.0 _.1 1) (_.2 _.3 1))
                  ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))
                  ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 1))))

              (ftest "testc21.tex-12" 
                (run+ (t)
                  (exist (y z)
                    (=lo `(1 . ,y) `(0 1 1 0 1 . ,z))
                    (== `(,y ,z) t)))
                `(((_.0 _.1 _.2 1) ())
                  ((_.0 _.1 _.2 _.3 1) (1))
                  ((_.0 _.1 _.2 _.3 _.4 1) (_.5 1))
                  ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 1))
                  ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1) (_.7 _.8 _.9 1))))

              (letrec ((<lo
                         (lambda (n m)
                           (conde
                             ((== '() n) (poso m))
                             ((== '(1) n) (>1o m))
                             ((exist (a x b y)
                                (== `(,a . ,x) n) (poso x)
                                (== `(,b . ,y) m) (poso y)
                                (<lo x y)))))))

                (ftest "testc21.tex-13" 
                  (run+ (t)
                    (exist (y z)
                      (<lo `(1 . ,y) `(0 1 1 0 1 . ,z))
                      (== `(,y ,z) t)))
                  `((() _.0)
                    ((1) _.0)
                    ((_.0 1) _.1)
                    ((_.0 _.1 1) _.2)
                    ((_.0 _.1 _.2 1) (_.3 . _.4))
                    ((_.0 _.1 _.2 _.3 1) (_.4 _.5 . _.6))
                    ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 . _.8))
                    ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 _.8 _.9 . _.10))))

                (dtest "testc21.tex-14"
                  (run 1 (n)
                    (<lo n n)))

                (letrec ((<=lo
                        (lambda (n m)
                          (conde
                            ((=lo n m))
                            ((<lo n m))))))

                  (ftest "testc21.tex-15" 
                    (run+ (t)
                      (exist (n m)
                        (<=lo n m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (1))
                      (() (_.0 . _.1))
                      ((1) (_.0 _.1 . _.2))
                      ((_.0 1) (_.1 1))
                      ((_.0 1) (_.1 _.2 _.3 . _.4))
                      ((_.0 _.1 1) (_.2 _.3 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))))

                  (ftest "testc21.tex-16" 
                    (run+ (t)
                      (exist (n m)
                        (<=lo n m)
                        (*o n '(0 1) m)
                        (== `(,n ,m) t)))
                    (list `(() ())))

                  (ftest "testc21.tex-17" 
                    (run+ (t)
                      (exist (n m)
                        (<=lo n m)
                        (*o n '(0 1) m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (0 1))
                      ((0 1) (0 0 1))
                      ((1 1) (0 1 1))
                      ((1 _.0 1) (0 1 _.0 1))
                      ((0 0 1) (0 0 0 1))
                      ((0 1 1) (0 0 1 1))
                      ((1 _.0 _.1 1) (0 1 _.0 _.1 1))
                      ((0 1 _.0 1) (0 0 1 _.0 1))
                      ((0 0 0 1) (0 0 0 0 1))))

                  (ftest "testc21.tex-18" 
                    (run+ (t)
                      (exist (n m)
                        (<=lo n m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (1))
                      (() (_.0 . _.1))
                      ((1) (_.0 _.1 . _.2))
                      ((_.0 1) (_.1 1))
                      ((_.0 1) (_.1 _.2 _.3 . _.4))
                      ((_.0 _.1 1) (_.2 _.3 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))
                      ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . _.6))
                      ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . _.8))
                      ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 _.8 _.9 1))
                      ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . _.10))
                      ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 _.8 _.9 _.10 _.11 1))
                      ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 _.8 _.9 _.10 _.11 . _.12))))
                  
                (letrec ((<o
                           (lambda (n m)
                             (conde
                               ((<lo n m))
                               ((=lo n m)
                                (exist (x)
                                  (poso x)
                                  (pluso n x m))))))
                         
                         (<=o
                           (lambda (n m)
                             (conde
                               ((== n m))
                               ((<o n m))))))

                  (mtest "testc21.tex-19" 
                    (run* (q)
                      (<o '(1 0 1) '(1 1 1))
                      (== #t q))
                    (list #t))

                  (mtest "testc21.tex-20" 
                    (run* (q)
                      (<o '(1 1 1) '(1 0 1))
                      (== #t q))
                    `())

                  (mtest "testc21.tex-21" 
                    (run* (q)
                      (<o '(1 0 1) '(1 0 1))
                      (== #t q))
                    `())

                  (mtest "lessthanequalo-1"
                    (run* (q)
                      (<=o '(1 0 1) '(1 0 1))
                      (== #t q))
                    `(#t))

                  (mtest "testc21.tex-22" 
                    (run* (n)
                      (<o n `(1 0 1)))
                    `(() (1) (_.0 1) (0 0 1)))

                  (mtest "testc21.tex-23" ;(skip "<o looping")
                    (run* (m)
                      (<o `(1 0 1) m))
                    `((_.0 _.1 _.2 _.3 . _.4) (0 1 1) (1 1 1)))

                  (dtest "testc21.tex-24"
                    (run* (n)
                      (<o n n)))

                  (letrec ((/o
                    (lambda (n m q r)
                      (conde
                        ((== '() q) (== n r) (<o n m))
                        ((== '(1) q) (== '() r) (== n m)
                         (<o r m))      
                        ((<o m n) (<o r m)
                         (exist (mq)
                           (<=lo mq n)
                           (*o m q mq)
                           (pluso mq r n))))))

                           (/otest1
                             (lambda ()
                               (run 3 (t)
                                 (exist (y z)
                                   (/o `(1 0 . ,y) '(0 1) z '())
                                   (== `(,y ,z) t))))))
                    (dtest "testc23.tex-/otest1"
                      (/otest1)))

                  (letrec
                    ((/o
                       (lambda (n m q r)
                         (conde
                           ((== r n) (== '() q) (<o n m))
                           ((== '(1) q) (=lo n m) (pluso r m n)
                            (<o r m))
                           ((<lo m n)                        
                            (<o r m)                        
                            (poso q)                 
                            (exist (nh nl qh ql qlm qlmr rr rh)
                              (splito n r nl nh)
                              (splito q r ql qh)
                              (conde
                                ((== '() nh)
                                 (== '() qh)
                                 (minuso nl r qlm)
                                 (*o ql m qlm))
                                ((poso nh)
                                 (*o ql m qlm)
                                 (pluso qlm r qlmr)
                                 (minuso qlmr nl rr)
                                 (splito rr r '() rh)
                                 (/o nh m qh rh))))))))

                     (splito
                       (lambda (n r l h)
                         (conde
                           ((== '() n) (== '() h) (== '() l))
                           ((exist (b n^)
                              (== `(0 ,b . ,n^) n)
                              (== '() r)
                              (== `(,b . ,n^) h)
                              (== '() l)))
                           ((exist (n^)
                              (==  `(1 . ,n^) n)
                              (== '() r)
                              (== n^ h)
                              (== '(1) l)))
                           ((exist (b n^ a r^)
                              (== `(0 ,b . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== '() l)
                              (splito `(,b . ,n^) r^ '() h)))
                           ((exist (n^ a r^)
                              (== `(1 . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== '(1) l)
                              (splito n^ r^ '() h)))
                           ((exist (b n^ a r^ l^)
                              (== `(,b . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== `(,b . ,l^) l)
                              (poso l^)
                              (splito n^ r^ l^ h)))))))

                    (ftest "testc21.tex-25" 
                      (run+ (t)
                        (exist (n m q r)
                          (/o n m q r)
                          (== `(,n ,m ,q ,r) t)))
                      `((() (_.0 . _.1) () ())
                        ((1) (_.0 _.1 . _.2) () (1))
                        ((_.0 1) (_.1 _.2 _.3 . _.4) () (_.0 1))
                        ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . _.6) () (_.0 _.1 1))
                        ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . _.8) () (_.0 _.1 _.2 1))
                        ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . _.10) () (_.0 _.1 _.2 _.3 1))))

                    (letrec
                      ((appendo
                         (lambda (l s out)
                           (conde
                             ((nullo l) (== s out))
                             ((exist (a d res)
                                (conso a d l)
                                (conso a res out)
                                (appendo d s res))))))
                       (logo
                         (lambda (n b q r)
                           (conde
                             ((== '(1) n) (poso b) (== '() q) (== '() r))
                             ((== '() q) (<o n b) (pluso r '(1) n))
                             ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                             ((== '(1) b) (poso q) (pluso r '(1) n))
                             ((== '() b) (poso q) (== r n))
                             ((== '(0 1) b)
                              (exist (a ad dd)
                                (poso dd)
                                (== `(,a ,ad . ,dd) n)
                                (exp2 n '() q)
                                (exist (s)
                                  (splito n dd r s))))
                             ((exist (a ad add ddd)
                                (conde
                                  ((== '(1 1) b))
                                  ((== `(,a ,ad ,add . ,ddd) b))))
                              (<lo b n)
                              (exist (bw1 bw nw nw1 ql1 ql s)
                                (exp2 b '() bw1)
                                (pluso bw1 '(1) bw)
                                (<lo q n)
                                (exist (q1 bwq1)
                                  (pluso q '(1) q1)
                                  (*o bw q1 bwq1)
                                  (<o nw1 bwq1))
                                (exp2 n '() nw1)
                                (pluso nw1 '(1) nw)
                                (/o nw bw ql1 s)
                                (pluso ql '(1) ql1)
                                (<=lo ql q)
                                (exist (bql qh s qdh qd)
                                  (repeated-mul b ql bql)
                                  (/o nw bw1 qh s)
                                  (pluso ql qdh qh)
                                  (pluso ql qd q)
                                  (<=o qd qdh)
                                  (exist (bqd bq1 bq)
                                    (repeated-mul b qd bqd)
                                    (*o bql bqd bq)
                                    (*o b bq bq1)
                                    (pluso bq r n)
                                    (<o n bq1))))))))

                       (exp2
                         (lambda (n b q)
                           (conde
                             ((== '(1) n) (== '() q))
                             ((>1o n) (== '(1) q)
                              (exist (s)
                                (splito n b s '(1))))
                             ((exist (q1 b2)
                                (== `(0 . ,q1) q)
                                (poso q1)
                                (<lo b n)
                                (appendo b `(1 . ,b) b2)
                                (exp2 n b2 q1)))
                             ((exist (q1 nh b2 s)
                                (== `(1 . ,q1) q)
                                (poso q1)
                                (poso nh)
                                (splito n b s nh)
                                (appendo b `(1 . ,b) b2)
                                (exp2 nh b2 q1))))))

                       (repeated-mul
                         (lambda (n q nq)
                           (conde
                             ((poso n) (== '() q) (== '(1) nq))
                             ((== '(1) q) (== n nq))
                             ((>1o q)
                              (exist (q1 nq1)
                                (pluso q1 '(1) q)
                                (repeated-mul n q1 nq1)
                                (*o nq1 n nq)))))))

                      (mtest "testc21.tex-26"  ;(skip "logo looping")
                        (run* (r) 
                          (logo '(0 1 1 1) '(0 1) '(1 1) r))
                        (list `(0 1 1)))
                      
                      (ftest "testc21.tex-27" ;(skip "logo looping")
                        (run+ (s)
                          (exist (b q r)
                            (logo '(0 0 1 0 0 0 1) b q r)
                            (>1o q)
                            (== `(,b ,q ,r) s)))
                        `((() (_.0 _.1 . _.2) (0 0 1 0 0 0 1))
                          ((1) (_.0  _.1 . _.2) (1 1 0 0 0 0 1))
                          ((0 1) (0 1 1) (0 0 1))
                          ((1 1) (1 1) (1 0 0 1 0 1))
                          ((0 0 1) (1 1) (0 0 1))
                          ((0 0 0 1) (0 1) (0 0 1))
                          ((1 0 1) (0 1) (1 1 0 1 0 1))
                          ((0 1 1) (0 1) (0 0 0 0 0 1))
                          ((1 1 1) (0 1) (1 1 0 0 1))))

                      (let ((expo (lambda (b q n)
                                    (logo n b q '()))))
                        (mtest "testc21.tex-28" ;(skip "expo looping")
                          (run* (t)
                            (expo '(1 1) '(1 0 1) t))
                          (list `(1 1 0 0 1 1 1 1))))
                      
                      )))))))))))))))))))

(letrec ((proof-that-exist-needs-an-inc
           (exist ()
             (proof-that-exist-needs-an-inc))))
  (mtest 'proof-that-run-needs-an-inc
    (run 1 (q)
      (conde
        (proof-that-exist-needs-an-inc)
        ((== #f #f))))
    '(_.0))

  (mtest 'proof-that-run-needs-an-inc-with-conde
    (run 1 (q)
      (conde
        (proof-that-exist-needs-an-inc (== #f #f))
        ((== #f #f))))
    '(_.0)))

(mtest 'why-conde-must-also-have-an-inc
  (run 5 (q) 
    (letrec ((f (exist () 
                  (conde 
                    (f (conde 
                         (f) 
                         ((== #f #f)))) 
                    ((== #f #f)))))) 
      f))
  '(_.0 _.0 _.0 _.0 _.0))

(test "testc22.tex-19" 
  (run* (q)
    (== #f q)
    (project (q)
      (== (not (not q)) q)))
  '(#f))

(dtest "testc22.tex-25"
  (run 1 (x)
    (==-no-check `(,x) x)))

(mtest "testc22.tex-26"   
  (run* (q) 
    (exist (x)
      (==-no-check `(,x) x)
      (== #t q)))
  `(#t))

(mtest "testc22.tex-27"   
  (run* (q)
    (exist (x y)
      (==-no-check `(,x) y)
      (==-no-check `(,y) x)
      (== #t q)))
  `(#t))

(mtest "testc22.tex-27-check"
  (run* (q)
    (exist (x y)
      (==-check `(,x) y)
      (==-check `(,y) x)
      (== #t q)))
  `())

(mtest "testc22.tex-27-==-default"
  (let ((occurs-check-present? ==-check))
    (run* (q)
      (exist (x y)
        (== `(,x) y)
        (== `(,y) x)
        (== #t q))))
  `())

(test "testc22.tex-28"   
  (run 1 (x) 
    (==-check `(,x) x))
  `())

(dtest "testc22.tex-29"
  (run 1 (x)
    (exist (y z)
      (== x z)
      (== `(a b ,z) y)
      (==-no-check x y))))

(test "testc22.tex-30" 
  (run 1 (x)
    (exist (y z)
      (== x z)
      (== `(a b ,z) y)
      (==-check x y)))
  `())

#!eof
;(print "DONE" nl "SKIPPED: " (skipped-tests) nl) #!eof

(mtest "bobo0" (skip "subsumption")
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((exist (bo) (b i o) (b o bo)))))))
    (run 2 (q)
      (exist (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) (0 . _.0))))

I think everything below is testing unexported/non-declarative features.

(define gen&testo
  (lambda (op i j k)
    (onceo
      (exist (x y z)
        (op x y z)
        (== i x)
        (== j y)
        (== k z)))))

(test-check "testc23.tex-19" 
(run* (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(1 1 1))
  (== #t q))

(list 
#t
))
(define e (make-engine (lambda () 
(run1 (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(0 1 1)))
)))
(printf "Testing testc23.tex-20  (engine with ~s ticks fuel)\n" max-ticks)
(e max-ticks
(lambda (t v) (error 'testc23.tex-20 "infinite loop returned ~s after ~s ticks" v (- max-ticks t)))
(lambda (e^) (void)))

(define e (make-engine (lambda () 
(run1 (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(0 1 1)))
)))
(printf "Testing testc23.tex-21  (engine with ~s ticks fuel)\n" max-ticks)
(e max-ticks
(lambda (t v) (error 'testc23.tex-21 "infinite loop returned ~s after ~s ticks" v (- max-ticks t)))
(lambda (e^) (void)))


(define enumerateo
  (lambda (op r n)
    (exist (i j k)
      (bumpo n i)
      (bumpo n j)
      (op i j k)
      (gen&testo op i j k)
      (== `(,i ,j ,k) r))))


(test-check "testc23.tex-22" 
(run* (s)
  (enumerateo pluso s '(1 1)))


`(((1 1) (1 1) (0 1 1))
 ((1 1) (0 1) (1 0 1))
 ((1 1) () (1 1))
 ((0 1) (1 1) (1 0 1))
 ((1 1) (1) (0 0 1))
 ((1) (1 1) (0 0 1))
 ((0 1) (0 1) (0 0 1))
 (() (1 1) (1 1))
 ((0 1) () (0 1))
 ((0 1) (1) (1 1))
 ((1) (0 1) (1 1))
 ((1) (1) (0 1))
 ((1) () (1))
 (() (0 1) (0 1))
 (() (1) (1))
 (() () ()))
)

(run* (s)
  (enumerateo pluso s '(1 1)))


(test-check "testc23.tex-23" 
(run1 (s)
  (enumerateo pluso s '(1 1 1)))


`(((1 1 1) (1 1 1) (0 1 1 1)))
)

(test-check "testc22.tex-4" 
(walk z `((,z . a) (,x . ,w) (,y . ,z)))
'a)

(test-check "testc22.tex-5"   
(walk y `((,z . a) (,x . ,w) (,y . ,z)))
'a)

(test-check "testc22.tex-6"   
(walk x `((,z . a) (,x . ,w) (,y . ,z)))
w)

(test-check "testc22.tex-7"   
(walk w `((,z . a) (,x . ,w) (,y . ,z)))
w)

(test-check "testc22.tex-8"   
(walk u `((,x . b) (,w . (,x e ,x)) (,u . ,w)))
`(,x e ,x))


(test-check "testc22.tex-9" 
(walk y (ext-s x 'e `((,z . ,x) (,y . ,z))))
'e)

(test-check "testc22.tex-10"                                                    
(walk y `((,x . e)))                                                            
y)

(test-check "testc22.tex-11"   
(walk x `((,y . ,z) (,x . ,y)))
z)

(test-check "testc22.tex-12"   
(walk x (ext-s y z `((,x . ,y))))
z)

(test-check "testc22.tex-13" 
(walk x (ext-s z 'b `((,y . ,z) (,x . ,y))))
'b)

(test-check "testc22.tex-14" 
(walk x (ext-s z w `((,y . ,z) (,x . ,y))))
w)


(test-check "testc22.tex-15" 
(occurs-check z u 
  `((,x . (a ,y)) (,w . (,x e ,x)) (,u . ,w) (,y . (,z))))
#t)

(test-check "testc22.tex-16"   
(walk* x
  `((,y . (a ,z c)) (,x . ,y) (,z . a)))
`(a a c))

(test-check "testc22.tex-17" 
(walk* x
  `((,y . (,z ,w c)) (,x . ,y) (,z . a)))
`(a ,w c))

(test-check "testc22.tex-18" 
(walk* y
  `((,y . (,w ,z c)) (,v . b) (,x . ,v) (,z . ,x)))
`(,w b c))

(test-check "testc22.tex-20" 
(let ((r (walk* `(,x ,y ,z) empty-s)))
  (walk* r (reify-s r empty-s)))
`(_.0 _.1 _.2))

(test-check "testc22.tex-21" 
(let ((r `(,u (,v (,w ,x) ,y) ,x)))
  (walk* r (reify-s r empty-s)))
`(_.0 (_.1 (_.2 _.3) _.4) _.3))

(test-check "testc22.tex-22" 
(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . a))))
  (let ((r (walk* x s)))
    (walk* r (reify-s r empty-s))))
`(a _.0 c _.0))

(test-check "testc22.tex-23" 
(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . ,u))))
  (let ((r (walk* x s)))
    (walk* r (reify-s r empty-s))))
`(_.0 _.1 c _.1))

;(test-check "testc22.tex-24" 
;(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . a))))
;  (reify x s))
;`(a _.0 c _.0))
(define proof-that-exist-needs-an-inc-with-conda
  (conda
    (proof-that-exist-needs-an-inc)))

(test-check 'proof-that-run-needs-an-inc-with-conde-and-conda
  (run 1 (q)
    (conde
      (proof-that-exist-needs-an-inc)
      ((== #f #f))))
  '(_.0))

(define proof-that-exist-needs-an-inc-with-conda
  (exist ()
    (conda
      (proof-that-exist-needs-an-inc (== #f #f)))))
