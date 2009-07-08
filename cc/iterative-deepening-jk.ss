(load "note-aux.ss")

;; G = N x S -> List(T)
;; T = N x S + N x G x S

;; (There is a side condition that given a goal g, the threads in the
;; list (g d s) have depth (d+1).)

(define debug-jk #t)

(define-syntax case-thread
  (syntax-rules ()
    ((_ e ((d1 a) e1) ((d2 g s) e2))
     (let ((v e))
       (let ((d (car v)) (t (cdr v)))
	 (cond
	  ((not (and (pair? t) (procedure? (car t)))) (let ((d1 d) (a t)) e1))
	  (else (let ((d2 d) (g (car t)) (s (cdr t))) e2))))))))

(define succeed (lambda (d s) `((,(add1 d) . ,s)))) ;; G also called unit.
(define fail (lambda (d s) '())) ;; G

;; N x G x S -> T (undone)
(define-syntax thread
  (syntax-rules ()
    ((_ d g s) `(,d ,g . ,s)))) 

;; N x G x G x S -> T  (syntax sugar, calls thread, used in bind)
(define-syntax thread/2g
  (syntax-rules ()
    ((_ d g1 g2 s) 
     (thread d (lambda (d s^) (bind (g1 d s^) g2)) s))))

(define-syntax bounce ;; G -> G
  (syntax-rules ()
    ((_  g-exp) (lambda (d s) `(,(thread d g-exp s))))))

;; Switch recvr and g to switch between DFS and BFS. 
(define bind 
  (lambda (comp recvr)
    (cond
      ((null? comp) '())
      (else (cons (case-thread (car comp)
		     ((d s) (thread d recvr s))
;		     ((d g s) (thread/2g d recvr g s))) ;; BFS
		     ((d g s) (thread/2g d g recvr s))) ;; DFS
		    (bind (cdr comp) recvr))))))

;; Checks whether a List(T) contains a thread whose depth is less than
;; max.  This is how we figure out whether we've exhausted
;; computations up to a certain depth.
(define giveup?
  (lambda (comp max)
    (cond
     ((null? comp) #f)
     (else (or (> (caar comp) max) (giveup? (cdr comp) max))))))


(define trampoline ;; G x N -> Stream(S) + {#f}
  (lambda (g max)
    (let tramp ((d 0) (tq ((bounce g) 0 empty-s))) ;; N x List(T) -> Stream(S) + {#f}
      (cond
        ((null? tq) '())
	((> d max) '())
	((giveup? tq max) #f)
        (else (case-thread (car tq)
                ((d^ s) (cons s (lambda () (tramp d^ (cdr tq)))))
                ((d^ g s) (let ((lst (g d s)))
			   (tramp d^ (append (cdr tq) lst))))))))))

(define-syntax disj ;; G x G -> G
  (syntax-rules ()
    ((_ g1 g2) (bounce (lambda (d s) (append (g1 (add1 d) s) (g2  (add1 d) s)))))))

(define-syntax conj ;; G x G -> G
  (syntax-rules ()
    ((_ g1 g2) (bounce (lambda (d s) (bind (g1 (add1 d) s) g2))))))

(define-syntax run/1 ;; (Num x var x G) -> List(Value)
  (syntax-rules ()
    ((_ n-exp (x) g)
     (let ((x (var 'x)) (max 5) (n-val n-exp))
       (printf-jk "Initial start with max depth ~s~%" max)
       (let take ((d max) (n n-val) (s-inf (trampoline g max)) (ans '()))
	 (cond
	  ((null? s-inf) (reverse ans))
	  ((not s-inf) (let ((d (+ d max)))
			 (printf-jk "Starting over with max depth ~s~%" d)
			 (take d n-val (trampoline g d) '())))
	  (else (let ((ans (cons (reify-jk (walk* x (car s-inf))) ans)))
		  (if (and n (= n 1)) (reverse ans)
		      (take d (and n (- n 1)) ((cdr s-inf)) ans))))))))))

;; Jiho's Debug code...
(define printf-jk
  (if debug-jk printf list))

(define reify-jk
 (lambda (v)
   (let ((v (reify v)))
     (printf-jk "~s~%" v)
     v)))

;; == needs to be redefined since the type of G changed.
(define ==
  (lambda (v w)
    (lambda (d s)
      (let ((s (unify v w s)))
	(if s (succeed d s) '())))))


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
  (run/1 1 (q) (conj (== q 1) (== q 2)))
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

; (test-check (lambda (s)
;               (letrec ((foo (lambda (s^) ((disj foo succeed) s^))))
;                 ((conj foo fail) s)))
;   (run/1 1 (q)
;     (lambda (n s)
;       (letrec ((foo (lambda (n s^) ((disj foo succeed) s^))))
;         ((conj foo fail) s))))
;   '())

; (test-check (lambda (s)
;               (letrec ((foo (lambda (s^) ((disj foo (== 1 q)) s^))))
;                 ((conj foo (== 1 q)) s)))
;   (run/1 1 (q)
;     (lambda (s)
;       (letrec ((foo (lambda (s^) ((disj foo (== 1 q)) s^))))
;         ((conj foo (== 1 q)) s))))
;   '(1))

; (test-check (lambda (s)
;               (letrec ((foo (disj foo succeed)))
;                 ((conj foo fail) s)))
;   (run/1 1 (q)  ;;; an eta; recall that bounce is curried.
;     (lambda (s)
;       (letrec ((foo (disj foo succeed)))
;         ((conj foo fail) s))))
;   '())

; (test-check (lambda (s)
;               (letrec ((foo (disj foo (== 1 q))))
;                 ((conj foo (== 1 q)) s)))
;   (run/1 1 (q) ;;; still the same eta
;     (lambda (s)
;       (letrec ((foo (disj foo (== 1 q))))
;         ((conj foo (== 1 q)) s))))
;   '(1))

; (test-check (letrec ((foo (disj foo (== 1 q))))
;               (lambda (s)
;                 ((conj foo (== 1 q)) s)))
;   (run/1 1 (q) ;;; pulled foo out
;     (letrec ((foo (disj foo (== 1 q))))
;       (lambda (s)
;         ((conj foo (== 1 q)) s))))
;   '(1))

; (test-check (letrec ((foo (disj foo (== 1 q))))
;               (conj foo (== 2 q)))
;   (run/1 1 (q) ;;; loops as expected
;     (letrec ((foo (disj foo (== 1 q))))
;       (conj foo (== 1 q))))
;   '(1))

; (test-divergence (letrec ((foo (disj foo (== 1 q))))
;                    (conj foo (== 1 q)))
;   (run/1 1 (q) ;;; via eta; look ma, no "s"s.
;     (letrec ((foo (disj foo (== 1 q))))
;       (conj foo (== 2 q)))))
; ;;;;

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

(test-check append-example-7
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

(test-check append-example-7-b
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

(test-check append-example-7-c
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

(test-check (conj
              (letrec ((l (lambda () (disj (l) (l)))))
                (l))
              (== #t #f))
  (run/1 2 (q)
    (conj
      (letrec ((l (lambda () (disj (l) (l)))))
        (l))
      (== #t #f)))
  '())

(test-check variant-b
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

(test-check variant-c
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

