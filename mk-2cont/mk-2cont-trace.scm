;  * goal: Sk -> Fk -> S -> S u { #f } 
;  * success continuation (Sk): Fk -> S -> S u { #f } 
;  * failure continuation (Fk): S -> S u { #f }  


(define-syntax lambdag@
  (syntax-rules ()
    ((_ (a b c) e) (lambda (a b c) e))))

(define-syntax lambdask@
  (syntax-rules ()
    ((_ sym (a b) e) (trace-lambda sym (a b) e))))

(define-syntax lambdafk@
  (syntax-rules ()
    ((_ sym () e) (trace-lambda sym () e))))

(define print-s
  (lambda ()
    (lambdag@ (sk fk s)
	      (begin (write s) (newline) (sk fk s)))))

(define var? vector?)
(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define empty-s '())
(define ext-s (lambda (x v s) (cons `(,x . ,v) s)))

(trace-define unify
  (lambda (v w s)
    (let ((v (walk v s)) (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s v w s))
        ((var? w) (ext-s w v s))
        ((and (pair? v) (pair? w))
         (let ((s (unify (car v) (car w) s)))
           (and s (unify (cdr v) (cdr w) s))))
        ((equal? v w) s)
        (else #f)))))

(define reify
  (lambda (t s)
    (let ((t (walk* t s)))
      (let ((s (reify-vars t)))
        (walk* t s)))))

(define walk*
  (lambda (t s)
    (let ((t (walk t s)))
      (if (pair? t)
        (cons
          (walk* (car t) s)
          (walk* (cdr t) s))
        t))))

(define reify-vars
  (lambda (t)
    (let rec ((t t) (s '()))
      (cond
        ((and (var? t) (not (assq t s)))
         (cons (cons t (reify-name (length s))) s))
        ((pair? t) (rec (cdr t) (rec (car t) s)))
        (else s)))))

(define reify-name
  (lambda (n) (string->symbol (string-append "_." (number->string n)))))


(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (cdr a) s))
           (else v))))
      (else v))))


(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) ...)
     (or+ (and+ g0 g ...) ...)]))

(define-syntax or+
  (syntax-rules ()
    [(_ g) g]
    [(_ g0 g ...) (or2 g0 (or+ g ...))]))

(define-syntax and+
  (syntax-rules ()
    [(_ g) g]
    [(_ g0 g ...) (and2 g0 (and+ g ...))]))

(define-syntax exist
  (syntax-rules ()
    [(_ () g0 g ...)
     (and+ g0 g ...)]
    [(_ (x0 x ...) g ...)
     (existfn 'x0 (lambda (x0)
                (exist (x ...) g ...)))]))

(define existfn
  (lambda (x var-g)
    (var-g (var x))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g g* ...)
     (let ((q (var 'q)))
       (let ((sk (lambdask@ 'run-sk (fk s) (cons (reify q s) fk)))
             (fk (lambdafk@ 'run-fk () #f)))
         (if (and n (zero? n)) '()
             (take n ((conde (g g* ...)) sk fk empty-s))))))))

(trace-define take
  (lambda (n v)
    (cond
      ((and n (zero? n)) '())
      ((not v) '())
      (else (cons (car v) (take (and n (- n 1)) ((cdr v))))))))

(trace-define and2
  (lambda (g1 g2)
    (lambdag@ (sk fk s)
      (g1 (lambdask@ 'and2-sk (fk^ s^) (g2 sk fk^ s^))
	  (lambdafk@ 'and2-fk () (fk))
	  s))))

(trace-define or2
  (lambda (g1 g2)
    (lambdag@ (sk fk s)
      (g1 (lambdask@ 'or2-sk (fk^ s^) (sk fk^ s^))
	  (lambdafk@ 'or2-fk () (g2 sk fk s))
	  s))))

(define ==
  (lambda (u v)
    (lambdag@ (sk fk s)
       (cond
	((unify u v s) => (lambda (s^) (sk fk s^)))
	(else (fk))))))

(define succeed (== #f #f))
(define fail (== #f #t))



