(library (minikanren disequality)
  (export run run* run+ conde exist =/= == ==-check)
  (import (rnrs) (rnrs records syntactic))

  (define-syntax lambdaf@ (syntax-rules () ((_ () e) (lambda () e))))
  (define-syntax lambdag@ (syntax-rules () ((_ (s) e) (lambda (s) e))))

  (define-record-type var (fields n))
  (define-record-type p (fields s c*))
  (define p/c* (lambda (p c*) (make-p (p-s p) c*)))
  (define empty-p (make-p '() '()))

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
             (lambdag@ (p) `(,(reify q p))))
           empty-p))))))

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
      (lambdag@ (p)
        (let ((s (unify u v (p-s p))))
          (and s
            (let ((c* (verify-c* (p-c* p) s)))
              (and c* (make-p s c*))))))))

  (define ==-check ==)

  (define s-extension
    (lambda (s^ s)
      (if (eq? s^ s) '()
        `(,(car s^) . ,(s-extension (cdr s^) s)))))

  (define =/=
    (lambda (u v)
      (lambdag@ (p)
        (cond
          ((unify u v (p-s p))
           => (lambda (s^)
                (let ((c (s-extension s^ (p-s p))))
                  (and (pair? c) (p/c* p `(,c . ,(p-c* p)))))))
          (else p)))))

  (define verify-c*
    (lambda (c* s)
      (let rec ((c* c*))
        (cond
          ((null? c*) '())
          ((unify-c (car c*) s)
           => (lambda (s^)
                (let ((c (s-extension s^ s)))
                  (and (pair? c) `(,c . ,(rec (cdr c*)))))))
          (else (rec (cdr c*)))))))

  (define unify-c
    (lambda (c s)
      (if (null? c) s
        (let ((s (unify (caar c) (cdar c) s)))
          (and s (unify-c (cdr c) s))))))

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
    (lambda (x t s)
      (cons `(,x . ,t) s)))

  (define ext-s-check
    (lambda (x t s)
      (and (not (occurs? x t s))
        (ext-s x t s))))

  (define occurs?
    (lambda (x t s)
      (let ((t (walk t s)))
        (cond
          ((var? t) (eq? x t))
          ((pair? t)
           (or
             (occurs? x (car t) s)
             (occurs? x (cdr t) s)))
          (else #f)))))

  (define unify
    (lambda (u v s)
      (let ((u (walk u s))
            (v (walk v s)))
        (cond
          ((eq? u v) s)
          ((var? u) (ext-s-check u v s))
          ((var? v) (ext-s-check v u s))
          ((and (pair? u) (pair? v))
           (let ((s (unify (car u) (car v) s)))
             (and s (unify (cdr u) (cdr v) s))))
          ((equal? u v) s)
          (else #f)))))

  (define-syntax exist
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambdag@ (p)
         (lambdaf@ ()
           (let ((x (make-var 'x)) ...)
             ((conde (g g* ...)) p)))))))

  (define-syntax conde
    (syntax-rules ()
      ((_ (g g+ ...) (g* g*+ ...) ...)
       (lambdag@ (p)
         (lambdaf@ ()
           (mplus*
             (bind* (g p) g+ ...)
             (bind* (g* p) g*+ ...) ...))))))

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
    (lambda (v p)
      (let ((v (walk* v (p-s p))))
        (let ((r (reifying-s v)))
          (let ((v (walk* v r))
                (c* (walk*
                      (remove-subsumed-c*
                        (purify-c* (walk* (p-c* p) (p-s p)) r))
                      r)))
            (if (pair? c*)
              `(,v (=/= . ,c*))
              v))))))

  (define purify-c*
    (lambda (c* r)
      (define ground?
        (lambda (t)
          (cond
            ((var? t) (not (var? (walk t r))))
            ((pair? t) (and
                         (ground? (car t))
                         (ground? (cdr t))))
            (else #t))))
      (filter ground? c*)))

  (define subsumed-c*?
    (lambda (c c*)
      (and (pair? c*)
        (or (eq? (unify-c (car c*) c) c)
          (subsumed-c*? c (cdr c*))))))

  (define remove-subsumed-c*
    (lambda (c*)
      (let rec ((c* c*) (a '()))
        (cond
          ((null? c*) a)
          ((or
             (subsumed-c*? (car c*) (cdr c*))
             (subsumed-c*? (car c*) a))
           (rec (cdr c*) a))
          (else (rec (cdr c*) `(,(car c*) . ,a))))))))
