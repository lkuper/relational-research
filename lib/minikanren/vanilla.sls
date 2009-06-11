(library (minikanren vanilla)
  (export run run* run+ conde exist == ==-no-check)
  (import (rnrs) (rnrs records syntactic))

  (define-syntax lambdaf@ (syntax-rules () ((_ () e) (lambda () e))))
  (define-syntax lambdag@ (syntax-rules () ((_ (s) e) (lambda (s) e))))

  (define-record-type var (fields n))

  ; term = var | scheme value | (term . term)
  ; s = ((var . term) ...)
  ; a-inf = #f | f | a | (a . f)
  ; f = () -> a-inf
  ; a = s | (answer)

  (define-syntax case-inf
    (syntax-rules ()
      ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
       (let ((a-inf e))
         (cond
           ((not a-inf) e0)
           ((procedure? a-inf) (let ((f^ a-inf)) e1))
           ((and (pair? a-inf) (procedure? (cdr a-inf)))
            (let ((a (car a-inf)) (f (cdr a-inf))) e3))
           (else (let ((a^ a-inf)) e2)))))))

  (define-syntax run
    (syntax-rules ()
      ((_ n (q) g g* ...)
       ((cond ((not n) take*) ((number? n) (take n)) (else take+))
        (lambdaf@ ()
          ((exist (q) g g* ...
             (lambdag@ (s) `(,(reify q s))))
           '()))))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q) g g* ...)
       (run #f (q) g g* ...))))

  (define-syntax run+
    (syntax-rules ()
      ((_ (q) g g* ...)
       (run #t (q) g g* ...))))

  (define (take n)
    (lambda (f)
      (if (zero? n) '()
        (case-inf (f)
          (() '())
          ((f) ((take n) f))
          ((a) (cons (car a) '()))
          ((a f) (cons (car a) ((take (- n 1)) f)))))))

  (define take*
    (lambda (f)
      (case-inf (f)
        (() '())
        ((f) (take* f))
        ((a) (cons (car a) '()))
        ((a f) (cons (car a) (take* f))))))

  (define take+
    (lambda (f)
      (case-inf (f)
        (() '())
        ((f) (take+ f))
        ((a) (cons (car a) (lambda () '())))
        ((a f) (cons (car a) (lambda () (take+ f)))))))

  (define ==
    (lambda (u v)
      (lambdag@ (s)
        (unify u v s))))

  (define ==-no-check ==)

  (define walk
    (lambda (t s0)
      (let rec ((t t) (s s0))
        (cond
          ((and (var? t)
             (pair? s)
             (not (eq? (cdar s) t)))
           (if (eq? (caar s) t)
             (rec (cdar s) s0)
             (rec t (cdr s))))
          (else t)))))

  (define ext-s
    (lambda (x v s)
      (cons `(,x . ,v) s)))

  (define unify
    (lambda (u v s)
      (let ((u (walk u s))
            (v (walk v s)))
        (cond
          ((eq? u v) s)
          ((var? u) (ext-s u v s))
          ((var? v) (ext-s v u s))
          ((and (pair? u) (pair? v))
           (let ((s (unify (car u) (car v) s)))
             (and s (unify (cdr u) (cdr v) s))))
          ((equal? u v) s)
          (else #f)))))

  (define-syntax exist
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambdag@ (s)
         (lambdaf@ ()
           (let ((x (make-var 'x)) ...)
             ((conde (g g* ...)) s)))))))

  (define-syntax conde
    (syntax-rules ()
      ((_ (g g+ ...) (g* g*+ ...) ...)
       (lambdag@ (s)
         (lambdaf@ ()
           (mplus*
             (bind* (g s) g+ ...)
             (bind* (g* s) g*+ ...) ...))))))

  (define-syntax bind*
    (syntax-rules ()
      ((_ a-inf) a-inf)
      ((_ a-inf g g* ...)
       (bind* (bind a-inf g) g* ...))))

  (define bind
    (lambda (a-inf g)
      (case-inf a-inf
        (() #f)
        ((f) (lambdaf@ () (bind (f) g)))
        ((a) (g a))
        ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

  (define-syntax mplus*
    (syntax-rules ()
      ((_ a-inf) a-inf)
      ((_ a-inf a-inf* ...)
       (mplus a-inf (lambdaf@ () (mplus* a-inf* ...))))))

  (define mplus
    (lambda (a-inf f)
      (case-inf a-inf
        (() (f))
        ((f^) (lambdaf@ () (mplus (f) f^)))
        ((a) (cons a f))
        ((a f^) (cons a (lambdaf@ () (mplus (f) f^)))))))

  (define walk*
    (lambda (w s)
      (let ((t (walk w s)))
        (cond
          ((pair? t)
           `(,(walk* (car t) s) .
             ,(walk* (cdr t) s)))
          (else t)))))

  (define reify-name
    (lambda (n) (string->symbol (string-append "_." (number->string n)))))

  (define reifying-s
    (lambda (t)
      (let rec ((t t) (s '()))
        (cond
          ((and (var? t) (not (assq t s)))
           (ext-s t (reify-name (length s)) s))
          ((pair? t) (rec (cdr t) (rec (car t) s)))
          (else s)))))

  (define reify
    (lambda (v s)
      (let ((v (walk* v s)))
        (walk* v (reifying-s v))))))
