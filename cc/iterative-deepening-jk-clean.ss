(load "note-aux.ss")

;; S = Substitutions
;; N = Natural numbers
;; G = N x S -> List(T)   (Goals)
;; T = N x S + N x G x S  (Threads)

;; (There is a side condition that given a goal g, the threads in the
;; list (g d s) have depth (d+1).)

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
(define thread (lambda (d g s) `(,d ,g . ,s)))

;; N x G x G x S -> T  (syntax sugar, used in bind)
(define thread/2g (lambda (d g1 g2 s) (thread d (lambda (d s^) (bind (g1 d s^) g2)) s)))

(define-syntax bounce ;; G -> G
  (syntax-rules ()
    ((_ g-exp) (lambda (d s) `(,(thread d g-exp s))))))

;; Switch recvr and g to switch between DFS and BFS. 
(define bind 
  (lambda (comp recvr)
    (cond
      ((null? comp) '())
      (else (cons (case-thread (car comp)
		     ((d s) (thread d recvr s))
		     ((d g s) (thread/2g d recvr g s))) ;; BFS
;		     ((d g s) (thread/2g d g recvr s))) ;; DFS
		    (bind (cdr comp) recvr))))))

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
       (let take ((d max) (n n-val) (s-inf (trampoline g max)) (ans '()))
	 (cond
	  ((null? s-inf) (reverse ans))
	  ((not s-inf) (let ((d (+ d max)))
			 (take d n-val (trampoline g d) '())))
	  (else (let ((ans (cons (reify-jk (walk* x (car s-inf))) ans)))
		  (if (and n (= n 1)) (reverse ans)
		      (take d (and n (- n 1)) ((cdr s-inf)) ans))))))))))


;; == needs to be redefined since the type of G changed.
(define ==
  (lambda (v w)
    (lambda (d s)
      (let ((s (unify v w s)))
	(if s (succeed d s) '())))))

