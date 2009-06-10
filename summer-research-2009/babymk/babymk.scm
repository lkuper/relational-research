(define-syntax lambdag@
  (syntax-rules ()
    ((_ (p) e) (lambda (p) e))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(define-syntax rhs
  (syntax-rules ()
    ((_ x) (cdr x))))

(define-syntax size-s
  (syntax-rules ()
    ((_ x) (length x))))

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define-syntax var?
  (syntax-rules ()
    ((_ x) (vector? x))))

(define-syntax mzero
  (syntax-rules () ((_) #f)))

(define-syntax choice
  (syntax-rules () ((_ a f) (cons a f))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((a f) e3))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         (else (let ((a (car a-inf)) (f (cdr a-inf)))
                 e3)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g)
     (take n ((existfn (lambda (x)
                         (and2 g
                               (project x
                                 (lambda (v)
                                   (lambdag@ (s)
                                     (singleton (cons (reify v) '()))))))))
              empty-s)))))

(define-syntax exist
  (syntax-rules ()
    [(_ () g0 g ...)
     (and+ g0 g ...)]
    [(_ (x0 x ...) g ...)
     (existfn (lambda (x0)
                (exist (x ...) g ...)))]))

(define existfn
  (lambda (var-g)
    (var-g (var 0))))

(define singleton
  (lambda (a)
    (choice a (lambda () #f))))

(define ==
  (lambda (u v)
    (lambdag@ (s)
      (cond
        [(unify u v s) => singleton]
        [else #f]))))

(define empty-s '())

(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (rhs a) s))
           (else v))))
      (else v))))

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define unify
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s v w s))
        ((var? w) (ext-s w v s))
        ((and (pair? v) (pair? w))
         (let ((s (unify (car v) (car w) s)))
           (and s (unify (cdr v) (cdr w) s))))
        ((equal? v w) s)
        (else #f)))))

(define unify-check
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify-check
                   (car u) (car v) s)))
           (and s (unify-check
                   (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (ext-s x v s)))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v)
         (or
          (occurs-check x (car v) s)
          (occurs-check x (cdr v) s)))
        (else #f)))))

(define walk*
  (lambda (w s)
    (let ((v (walk w s)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons
          (walk* (car v) s)
          (walk* (cdr v) s)))
        (else v)))))

(define reify-s
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v)
         (ext-s v (reify-name (size-s s)) s))
        ((pair? v) (reify-s (cdr v)
                            (reify-s (car v) s)))
        (else s)))))

(define reify-name
  (lambda (n)
    (string->symbol
     (string-append "_" "." (number->string n)))))

(define reify
  (lambda (v)
    (walk* v (reify-s v empty-s))))

(define ==-check
  (lambda (v w)
    (lambdag@ (s)
      (unify-check v w s))))

(define take
  (lambda (n a-inf)
    (case-inf a-inf
      (() '())
      ((a f)
       (if (and n (= 1 n))
           a
           (cons (car a)
                 (take (and n (- n 1)) (f))))))))

(define-syntax and+
  (syntax-rules ()
    [(_ g) g]
    [(_ g0 g ...) (and2 g0 (and+ g ...))]))

(define and2
  (lambda (g1 g2)
    (lambda (s)
      (bind (g1 s) g2))))

(define bind
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzero))
      ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

(define or2
  (lambda (g1 g2)
    (lambda (s)
      (mplus (g1 s) (lambdaf@ () (g2 s))))))

(define mplus
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((a f^) (choice a (lambdaf@ () (mplus (f) f^)))))))

(define project
  (lambda (x var-g)
    (lambdag@ (s)
      ((var-g (walk* x s)) s))))

(define succeed (== #f #f))

(define fail (== #f #t))
