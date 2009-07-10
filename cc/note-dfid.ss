(load "note-aux-dfid.ss")

;; G = D x S -> List(T)
;; T = (D x S) + (G x D x S)

(define-syntax case-thread
  (syntax-rules ()
    ((_ e ((d a) e1 ...) ((g d^ s) e2 ...))
     (let ((t e))
       (let ((l (length t)))
         (cond
           ((= l 3) (let ((g (car t)) (d^ (cadr t)) (s (caddr t))) (begin e2 ...)))
           (else (let ((d (car t)) (a (cadr t))) (begin e1 ...)))))))))

(define succeed  (lambda (d s) `((,d ,s)))) ;; D x S -> T also called unit.
(define fail (lambda (d s) '())) ;; G (?how is this so?)
(define thread (lambda (g d s) `(,g ,d ,s))) ;; G x D x S -> T (undone)

(define-syntax bounce ;; G -> List(T))
  (syntax-rules ()
    ((_ g-exp) (lambda (d s) `(,(thread g-exp d s))))))

;; Swap recvr and g in the (g d s) line to make it interleaved.
(define bind ;; (List(T) x G) -> List(T)
  (lambda (comp recvr)
    (cond
      ((null? comp) '())
      (else (case-thread (car comp)
              ((d s) (append (recvr d s) (bind (cdr comp) recvr)))
              ;((g d s) (let ((g^ (lambda (d^ s^) (bind (recvr d^ s^) g))))
              ((g d s) (let ((g^ (lambda (d^ s^) (bind (g d^ s^) recvr))))
                         (cons (thread g^ d s) (bind (cdr comp) recvr)))))))))

(define-syntax disj ;; G x G -> G
  (syntax-rules ()
    ((_ g1 g2) (bounce (lambda (d s) (append (g1 d s) (g2 d s)))))))

(define-syntax conj ;; G x G -> G
  (syntax-rules ()
    ((_ g1 g2) (bounce (lambda (d s) (bind (g1 d s) g2))))))

(define-syntax run/1 ;; (Num x var x G) -> List(Value)
  (syntax-rules ()
    ((_ n-exp (x) g^^)
     (let ((m n-exp) (x (var 'x)))
       (let tramp ((n m) (taken '()) (maxd 2) (tq ((bounce g^^) 0 empty-s)))
         (cond
           ((null? tq) (reverse taken))
           (else (case-thread (car tq)
                   ((d s)
                    (let ((taken (cons (reify (walk* x s)) taken)))
                      (if (and n (= n 1)) 
                        (reverse taken)   
                        (tramp (and n (- n 1)) taken maxd (cdr tq)))))
                   ((g d s)
                    (cond
                      ;((< d maxd) (tramp n taken maxd (append (cdr tq) (g (add1 d) s))))
                      ((< d maxd) (tramp n taken maxd (append (g (add1 d) s) (cdr tq))))
                      ((not (null? (cdr tq))) (tramp n taken maxd (cdr tq)))
                      (else (begin (printf "~d\n" maxd) (tramp m '() (* 2 maxd) ((bounce g^^) 0 empty-s))))))))))))))


;; == is also in the interface, but code for it is in note-aux.ss
;; exist is also in the interface, but code for it is in mktests.scm

;; Test programs

(define errorf
  (lambda (tag . args)
    (display "Failed: ") (display tag) (newline)
    (for-each  display args)
    (error 'WiljaCodeTester "That's all, folks!")))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (display "Testing ")
       (write 'title)
       (newline)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define-syntax test-divergence
  (syntax-rules ()
    ((_ title tested-expression)
     (let ((max-ticks 1000000))
       (printf "Testing ~s \n (engine with ~s ticks fuel)\n" 'title max-ticks)
       ((make-engine (lambda () tested-expression))
        max-ticks
        (lambda (t v)
     (error title "infinite loop returned ~s after ~s ticks"
                 v (- max-ticks t)))
        (lambda (e^) (void))))))) 

(test-check (conj succeed succeed)
  (run/1 1 (q) (conj succeed succeed))
  '(_.0))

(test-check (conj succeed (conj succeed fail))
  (run/1 1 (q) (conj succeed (conj succeed fail)))
  '())

(test-check (conj (conj succeed fail) succeed)
  (run/1 1 (q) (conj (conj succeed fail) succeed))
  '())

(test-check (conj (== q 1) (== q 2))
  (run/1 1 (w) (conj (== w 1) (== w 2)))
  '())

(test-check (conj (== q 1) (== q 1))
  (run/1 1 (q) (conj (== q 1) (== q 1)))
  '(1))

;; (gletrec ([foo (any foo succeed)])
;;    (all-int foo fail))

;; This would need a customized translation that would result in:

;; (strm-car
;;   (trampoline
;;      (lambda (subst)
;;         (letrec ([foo (lambda (subst) (bounce (any foo succeed) subst))])
;;           ((all-int foo fail) subst)))))

;(test-check (lambda (d s)
              ;(letrec ((foo (lambda (d s^) ((disj foo succeed) d s^))))
                ;((conj foo fail) d s)))
  ;(run/1 1 (q)
    ;(lambda (s)
      ;(letrec ((foo (lambda (s^) ((disj foo succeed) s^))))
        ;((conj foo fail) s))))
  ;'())
;
;(test-check (lambda (s)
              ;(letrec ((foo (lambda (s^ d) ((disj foo (== 1 q)) d s^))))
                ;((conj foo (== 1 q)) d s)))
  ;(run/1 1 (q)
    ;(lambda (s)
      ;(letrec ((foo (lambda (s^ d) ((disj foo (== 1 q)) d s^))))
        ;((conj foo (== 1 q)) d s))))
  ;'(1))
;
;#!eof
;(test-check (lambda (s)
              ;(letrec ((foo (disj foo succeed)))
                ;((conj foo fail) s)))
  ;(run/1 1 (q)  ;;; an eta; recall that bounce is curried.
    ;(lambda (s)
      ;(letrec ((foo (disj foo succeed)))
        ;((conj foo fail) s))))
  ;'())
;
;(test-check (lambda (s)
              ;(letrec ((foo (disj foo (== 1 q))))
                ;((conj foo (== 1 q)) s)))
  ;(run/1 1 (q) ;;; still the same eta
    ;(lambda (s)
      ;(letrec ((foo (disj foo (== 1 q))))
        ;((conj foo (== 1 q)) s))))
  ;'(1))
;
;(test-check (letrec ((foo (disj foo (== 1 q))))
              ;(lambda (s)
                ;((conj foo (== 1 q)) s)))
  ;(run/1 1 (q) ;;; pulled foo out
    ;(letrec ((foo (disj foo (== 1 q))))
      ;(lambda (s)
        ;((conj foo (== 1 q)) s))))
  ;'(1))

(test-check (letrec ((foo (disj foo (== 1 q))))
              (conj foo (== 2 q)))
  (run/1 1 (q) ;;; loops as expected
    (letrec ((foo (disj foo (== 1 q))))
      (conj foo (== 1 q))))
  '(1))

(test-divergence (letrec ((foo (disj foo (== 1 q))))
                   (conj foo (== 1 q)))
  (run/1 1 (q) ;;; via eta; look ma, no "s"s.
    (letrec ((foo (disj foo (== 1 q))))
      (conj foo (== 2 q)))))
;;;;

(test-check append-example-6
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (== l `(,a . ,d))
                      (conj
                        (appendo d s res)
                        (== out `(,a . ,res)))))))))
    (run/1 6 (q)
      (let ((x (var 'x)) (y (var 'y)))
        (conj
          (appendo x y '(cake with ice d t))
          (== q `(,x ,y))))))
   '((() (cake with ice d t))
     ((cake) (with ice d t))
     ((cake with) (ice d t))
     ((cake with ice) (d t))
     ((cake with ice d) (t))
     ((cake with ice d t) ())))

'(test-check append-example-7
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (== l `(,a . ,d))
                      (conj
                        (appendo d s res)
                        (== out `(,a . ,res)))))))))
    (run/1 7 (q)
      (let ((x (var 'x)) (y (var 'y)))
        (conj
          (appendo x y '(cake with ice d t))
          (== q `(,x ,y))))))
   '((() (cake with ice d t))
     ((cake) (with ice d t))
     ((cake with) (ice d t))
     ((cake with ice) (d t))
     ((cake with ice d) (t))
     ((cake with ice d t) ())))

'(test-check append-example-7-b
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (appendo d s res)
                      (conj
                        (== l `(,a . ,d))
                        (== out `(,a . ,res)))))))))
    (run/1 7 (q)
      (let ((x (var 'x)) (y (var 'y)))
        (conj
          (appendo x y '(cake with ice d t))
          (== q `(,x ,y))))))
  '((() (cake with ice d t))
    ((cake) (with ice d t))
    ((cake with) (ice d t))
    ((cake with ice) (d t))
    ((cake with ice d) (t))
    ((cake with ice d t) ())))

'(test-check append-example-7-c
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (conj
                        (appendo d s res)
                        (== l `(,a . ,d)))
                      (== out `(,a . ,res))))))))
    (run/1 7 (q)
      (let ((x (var 'x)) (y (var 'y)))
        (conj
          (appendo x y '(cake with ice d t))
          (== q `(,x ,y))))))
  '((() (cake with ice d t))
    ((cake) (with ice d t))
    ((cake with) (ice d t))
    ((cake with ice) (d t))
    ((cake with ice d) (t))
    ((cake with ice d t) ())))

'(test-check (conj
              (letrec ((l (lambda () (disj (l) (l)))))
                (l))
              (== #t #f))
  (run/1 2 (q)
    (conj
      (letrec ((l (lambda () (disj (l) (l)))))
        (l))
      (== #t #f)))
  '())

'(test-check variant-b
  (run/1 2 (q)
    (conj
      (letrec
        ((l (lambda ()
              (disj
                (l)
                (letrec
                  ((l (lambda ()
                        (disj (l) (l)))))
                    (l))))))
        (l))
      (== #f #t)))
  '())

'(test-check variant-c
  (run/1 #f (q)
    (conj
      (letrec ((l (lambda ()
                    (disj (l) (l)))))
        (l))
      (conj
        (letrec ((l (lambda ()
                      (disj (l) (l)))))
          (l))
        (== #f #t))))
  '())

(define anyo
  (lambda (g)
    (disj g (anyo g))))

(define nevero (anyo (== #t #f)))

(define alwayso (anyo (== #f #f)))

(define salo
  (lambda (g)
    (disj (== #f #f) g)))

(test-check (conj (salo nevero) (conj (== #t #f) (== #t q)))
  (run/1 1 (q)
    (conj
      (salo nevero)
      (conj
        (== #t #f)
        (== #t q))))
  '())

(test-check (conj alwayso (conj (== #t #f) (== #t q)))
  (run/1 1 (q)
    (conj
      alwayso
      (conj
        (== #t #f)
        (== #t q))))
  '())

(test-check (conj (disj (conj (== #f q) alwayso) (== #t q)) (== #t q))
  (run/1 2 (q) (conj (disj (conj (== #f q) alwayso) (== #t q)) (== #t q)))
  '(#t))

;;; wtests.scm

(test-check (== 5 q)
  (run/1 #f (q) (== q 5))
  '(5))

(test-check (run/1 #f (q) (conj (== 5 5) (== q 6)))
  (run/1 #f (q) (conj (== 5 5) (== q 6)))
  '(6))

(test-check (run/1 #f (q) (conj fail nevero))
  (run/1 #f (q) (conj fail nevero))
  '())

(test-check (run/1 #f (q) (conj nevero fail))
  (run/1 #f (q) (conj nevero fail))
  '())

(define neverw
  (letrec ((neverw (conj succeed neverw)))
    neverw))

(test-check (run/1 #f (q) (conj neverw fail))
  (run/1 #f (q) (conj neverw fail))
  '())

(test-divergence (run/1 #f (q) neverw)
  (run/1 #f (q) neverw))

(test-check (run/1 #f (q) (conj neverw (conj neverw (conj neverw fail))))
  (run/1 #f (q) (conj neverw (conj neverw (conj neverw fail))))
  '())

(test-check (run/1 #f (q) (conj neverw (conj neverw (conj fail neverw))))
  (run/1 #f (q) (conj neverw (conj neverw (conj fail neverw))))
  '())

(test-check (run/1 #f (q) (conj neverw (conj fail (conj neverw neverw))))
  (run/1 #f (q) (conj neverw (conj fail (conj neverw neverw))))
  '())

(test-check (run/1 #f (q) (conj fail (conj neverw (conj neverw neverw))))
  (run/1 #f (q) (conj fail (conj neverw (conj neverw neverw))))
  '())

;;funky!
(test-check (run/1 #f (q) (conj nevero (conj nevero (conj nevero fail))))
  (run/1 #f (q) (conj nevero (conj nevero (conj nevero fail))))
  '())

(test-check (run/1 #f (q) (conj nevero (conj nevero (conj fail nevero))))
  (run/1 #f (q) (conj nevero (conj nevero (conj fail nevero))))
  '())

(test-check (run/1 #f (q) (conj nevero (conj fail (conj nevero nevero))))
  (run/1 #f (q) (conj nevero (conj fail (conj nevero nevero))))
  '())

(test-check (run/1 #f (q) (conj fail (conj nevero (conj nevero nevero))))
  (run/1 #f (q) (conj fail (conj nevero (conj nevero nevero))))
  '())

(test-check (run/1 #f (q) (conj nevero (conj fail (conj neverw nevero))))
  (run/1 #f (q) (conj nevero (conj fail (conj neverw nevero))))
  '())

;;; allw tests These are from allwtests.scm

(test-check (run/1 #f (q) (disj (== q 1) (== q 2)))
  (run/1 #f (q) (disj (== q 1) (== q 2)))
  '(1 2))

(test-check conj1
  (run/1 #f (q)
    (let ((x (var 'x)) (y (var 'y)))
      (conj
        (disj
          (conj (== x 1) (== y 2))
          (conj (== x 2) (== y 1)))
        (== `(,x ,y) q))))
  '((1 2) (2 1)))

(test-check conj2
  (run/1 #f (q)
    (let ((x (var 'x)) (y (var 'y)))
      (conj
        (== `(,x ,y) q)
        (disj
          (conj (== x 1) (== y 2))
          (conj (== x 2) (== y 1))))))
  '((1 2) (2 1)))

(test-divergence (run/1 #f (q) (conj nevero nevero))
  (run/1 #f (q) (conj nevero nevero)))
  
(test-divergence (run/1 #f (q) (conj nevero alwayso))
  (run/1 #f (q) (conj nevero alwayso)))

(test-divergence (run/1 #f (q) (conj alwayso nevero))
  (run/1 #f (q) (conj alwayso nevero)))

(test-check (run/1 #f (q) (conj alwayso fail))
  (run/1 #f (q) (conj alwayso fail))
  '())

;;; Ron's tests

(test-check (run/1 #f (q) (conj fail nevero))
  (run/1 #f (q) (conj fail nevero))
  '())

(test-check (run/1 #f (q) (conj nevero fail))
  (run/1 #f (q) (conj nevero fail))
  '())

(test-check (run/1 #f (q) (conj (anyo fail) fail))
  (run/1 #f (q) (conj (anyo fail) fail))
  '())

(test-check (run/1 #f (q) (conj (anyo fail) fail))
  (run/1 #f (q) (conj (anyo fail) fail))
  '())

;;; Byrd 35

(define foo
  (lambda (x)
    (conj (== 5 x) (foo x))))

(define bar
  (lambda (x)
    (conj (bar x) (== 5 x))))

(define quux
  (lambda (x)
    (conj (== 5 x) (conj (quux x) (quux x)))))

(define quuux
  (lambda (x)
    (conj (quuux x) (conj (quuux x) (== 5 x)))))

(define blat
  (lambda (x)
    (conj (conj (blat x) (blat x)) (== 5 x))))

(test-check (run/1 #f (q) (conj fail alwayso))
  (run/1 #f (q) (conj fail alwayso))
  '())

(test-check (run/1 #f (q) (conj (== q 3) (== q 3)))
  (run/1 #f (q) (conj (== q 3) (== q 3)))
  '(3))

(test-check (run/1 #f (q) (conj (== q 3) (== q 4)))
  (run/1 #f (q) (conj (== q 3) (== q 4)))
  '())

(test-check (run/1 1 (q) (foo 6))
  (run/1 1 (q) (foo 6))
  '())

(test-check (run/1 #f (q) (foo 6))
  (run/1 #f (q) (foo 6))
  '())

(test-check (run/1 1 (q) (bar 6))
  (run/1 1 (q) (bar 6))
  '())

(test-check (run/1 #f (q) (quux 6))
  (run/1 #f (q) (quux 6))
  '())

(test-check (run/1 1 (q) (quuux 6))
  (run/1 1 (q) (quuux 6))
  '())

(test-check (run/1 #f (q) (blat 6))
  (run/1 #f (q) (blat 6))
  '())

(test-check appendo-ex1
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (== l `(,a . ,d))
                      (conj
                        (appendo d s res)
                        (== out `(,a . ,res)))))))))
    (run/1 5 (q)
      (let ((y (var 'y)) (z (var 'z)))
        (appendo q y z))))
   '(()
     (_.0)
     (_.0 _.1)
     (_.0 _.1 _.2)
     (_.0 _.1 _.2 _.3)))

(test-check "appendo-ex2"
  (letrec
    ((appendo (lambda (l s out)
                (disj
                  (conj (== '() l) (== s out))
                  (let ((a (var 'a)) (d (var 'd)) (res (var 'res)))
                    (conj
                      (== l `(,a . ,d))
                      (conj
                        (appendo d s res)
                        (== out `(,a . ,res)))))))))
    (run/1 5 (q)
      (let ((x (var 'x)) (y (var 'y)) (z (var 'z)))
        (conj (appendo x y z) (== `(,x ,y ,z) q)))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
    ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))

(define assqo
  (lambda (x ls out)
    (disj
      (conj
        (let ((a (var 'a)) (aa (var 'ss)))
          (conj
            (conj
              (caro ls a)
              (caro a aa))
             (== aa x)))
        (caro ls out))
      (let ((d (var 'd)))
        (conj
          (cdro ls d)
          (assqo x d out))))))

(define caro
  (lambda (ls a)
    (let ((d (var 'd)))
      (== `(,a . ,d) ls))))

(define cdro
  (lambda (ls d)
    (let ((a (var 'a)))
      (== `(,a . ,d) ls))))

(test-check (run/1 #f (q) (assqo 'x '((x . 5)) q))
  (run/1 #f (q) (assqo 'x '((x . 5)) q))
  '((x . 5)))

(test-check (run/1 #f (q) (assqo 'x '() q))
  (run/1 #f (q) (assqo 'x '() q))
  '())

(test-check (run/1 #f (q) (assqo 'x '((w . 3) (x . 5) (y . 7)) q))
  (run/1 #f (q) (assqo 'x '((w . 3) (x . 5) (y . 7)) q))
  '((x . 5)))

(test-check (assqo 'x '((y . #t) (x . 3) (x . 5) (z . #f) (x . 7)) q)
  (run/1 #f (q) (assqo 'x '((y . #t) (x . 3) (x . 5) (z . #f) (x . 7)) q))
  '((x . 3) (x . 5) (x . 7)))

(test-check (conj (assqo sym ls '(x . 3)) (== `(,sym ,ls) q))
  (run/1 5 (q)
    (let ((sym (var 'sym)) (ls (var 'ls)))
      (conj (assqo sym ls '(x . 3)) (== `(,sym ,ls) q))))
  '((x ((x . 3) . _.0))
    (x (_.0 (x . 3) . _.1))
    (x (_.0 _.1 (x . 3) . _.2))
    (x (_.0 _.1 _.2 (x . 3) . _.3))
    (x (_.0 _.1 _.2 _.3 (x . 3) . _.4))))

(test-check (conj (assqo sym ls `(x . ,v)) (== `(,sym ,ls) q))
  (run/1 5 (q)
    (let ((sym (var 'sym)) (ls (var 'ls)) (v (var 'v)))
      (conj (assqo sym ls `(x . ,v)) (== `(,sym ,ls) q))))
  '((x ((x . _.0) . _.1))
    (x (_.0 (x . _.1) . _.2))
    (x (_.0 _.1 (x . _.2) . _.3))
    (x (_.0 _.1 _.2 (x . _.3) . _.4))
    (x (_.0 _.1 _.2 _.3 (x . _.4) . _.5))))

(test-check (conj (assqo sym ls out) (== `(,sym ,ls ,out) q))
  (run/1 5 (q)
    (let ((sym (var 'sym)) (ls (var 'ls)) (out (var 'out)))
      (conj (assqo sym ls out) (== `(,sym ,ls ,out) q))))
  '((_.0 ((_.0 . _.1) . _.2) (_.0 . _.1))
    (_.0 (_.1 (_.0 . _.2) . _.3) (_.0 . _.2))
    (_.0 (_.1 _.2 (_.0 . _.3) . _.4) (_.0 . _.3))
    (_.0 (_.1 _.2 _.3 (_.0 . _.4) . _.5) (_.0 . _.4))
    (_.0 (_.1 _.2 _.3 _.4 (_.0 . _.5) . _.6) (_.0 . _.5))))

(define fail-immediately fail)

(define fail-almost-immediately (disj fail fail))

(define yikes0
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj succeed (conj fail-almost-immediately (yikes0 d res))))))

;;; Diverges
(test-check (run/1 #f (q) (yikes0 q '()))
  (run/1 #f (q) (yikes0 q '()))
  '())

(define yikes0-fi
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj succeed (conj fail-immediately (yikes0-fi d res))))))

;;; Terminates
(test-check (run/1 #f (q) (yikes0-fi q '()))
  (run/1 #f (q) (yikes0-fi q '()))
  '())

(define yikes1
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj succeed (conj fail-almost-immediately (yikes1 d res))))))

;;; Diverges
(test-check (run/1 #f (q) (yikes1 q '()))
  (run/1 #f (q) (yikes1 q '()))
  '())

(define yikes1-fi
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj succeed (conj fail-almost-immediately (yikes1-fi d res))))))

;;; Terminates
(test-check (run/1 #f (q) (yikes1-fi q '()))
  (run/1 #f (q) (yikes1-fi q '()))
  '())

