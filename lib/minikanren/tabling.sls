(library (minikanren tabling)
  (export run run* run+ conde exist ==-check ==-no-check == tabled project)
  (import (rnrs) (rnrs records syntactic))

  (define-syntax lambdaf@ (syntax-rules () ((_ () e) (lambda () e))))
  (define-syntax lambdag@ (syntax-rules () ((_ (s) e) (lambda (s) e))))

  ; term = var | scheme value | (term . term)
  ; s = ((var . term) ...)

  (define-record-type var (fields n s))

  (define subunify
    (lambda (arg ans s)
      (let ((arg (walk arg s)))
        (cond
          ((eq? arg ans) s)
          ((var? arg) (ext-s-no-check arg ans s)) ; no-check?
          ((pair? arg) (subunify (cdr arg) (cdr ans)
                         (subunify (car arg) (car ans) s)))
          (else s)))))

  (define alpha-equiv?
    (lambda (t1 t2 s)
      (equal?
        ((reify reify-name) t1 s)
        ((reify reify-name) t2 s))))

  (define-record-type cache (fields (mutable ansv*)))
  (define-record-type ss (fields cache ansv* f))

  (define reify-name
    (lambda (n) (string->symbol (string-append "_." (number->string n)))))

  (define (reify-var s)
    (lambda (n) (make-var n s)))

  (define reuse
    (lambda (argv cache s)
      (let fix ((start (cache-ansv* cache)) (end '()))
        (let rec ((ansv* start))
          (if (eq? ansv* end)
            (list (make-ss cache start (lambdaf@ () (fix (cache-ansv* cache) start))))
            (cons (subunify argv ((reify (reify-var s)) (car ansv*) s) s)
              (lambdaf@ () (rec (cdr ansv*)))))))))

  (define master
    (lambda (argv cache)
      (lambdag@ (s)
        (and
          (for-all
            (lambda (ansv) (not (alpha-equiv? argv ansv s)))
            (cache-ansv* cache))
          (begin
            (cache-ansv*-set! cache
              (cons ((reify (reify-var s)) argv s)
                (cache-ansv* cache)))
            s)))))

  (define-syntax tabled
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (let ((table '()))
         (lambda (x ...)
           (let ((argv `(,x ...)))
             (lambdag@ (s)
               (let ((key ((reify reify-name) argv s)))
                 (cond
                   ((assoc key table)
                    => (lambda (key.cache) (reuse argv (cdr key.cache) s)))
                   (else (let ((cache (make-cache '())))
                           (set! table `((,key . ,cache) . ,table))
                           ((conde (g g* ... (master argv cache))) s))))))))))))

  (define stored-shrink-walk
    (lambda (t start)
      (let rec ((t t) (s start) (end '()))
        (if (or (not (var? t))
              (eq? s (var-s t))
              (eq? s end))
          t
          (if (eq? (caar s) t)
            (rec (cdar s) start (cdr s))
            (rec t (cdr s) end))))))

  (define shrink-walk
    (lambda (t start)
      (let rec ((t t) (s start) (end '()))
        (if (or (not (var? t))
              (eq? s end))
          t
          (if (eq? (caar s) t)
            (rec (cdar s) start (cdr s))
            (rec t (cdr s) end))))))

  (define walk stored-shrink-walk)
  (define walk-no-br shrink-walk)

  (define (unify ext-s)
    (lambda (u v s)
      (let ((u (walk u s))
            (v (walk v s)))
        (cond
          ((eq? u v) s)
          ((var? u) (ext-s u v s))
          ((var? v) (ext-s v u s))
          ((and (pair? u) (pair? v))
           (let ((s ((unify ext-s) (car u) (car v) s)))
             (and s ((unify ext-s) (cdr u) (cdr v) s))))
          ((equal? u v) s)
          (else #f)))))

  (define ext-s-no-check
    (lambda (x t s)
      (cons `(,x . ,t) s)))

  (define ext-s-check
    (lambda (x t s)
      (and (not (occurs? x t s))
        (ext-s-no-check x t s))))

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

  (define (walk* walk)
    (lambda (w s)
      (let walk* ((w w) (s s))
        (let ((t (walk w s)))
          (cond
            ((pair? t)
             `(,(walk* (car t) s) .
               ,(walk* (cdr t) s)))
            (else t))))))

  (define reifying-s
    (lambda (rep t)
      (let rec ((t t) (s '()))
        (cond
          ((and (var? t) (not (assq t s)))
           (ext-s-no-check t (rep (length s)) s))
          ((pair? t) (rec (cdr t) (rec (car t) s)))
          (else s)))))

  (define (reify rep)
    (lambda (v s)
      (let ((v ((walk* walk) v s)))
        ((walk* walk-no-br) v (reifying-s rep v)))))

  (define-syntax run
    (syntax-rules ()
      ((_ n (q) g g* ...)
       (if (or (and (integer? n) (positive? n)) (boolean? n))
         ((cond ((not n) take*) ((number? n) (take n)) (else take+))
          (lambdaf@ ()
            ((exist (q) g g* ...
               (lambdag@ (s) (list ((reify reify-name) q s))))
             '())))
         (assertion-violation 'run "not a positive integer" n)))))

  ; stream = #f | f | w | a | (a . f)
  ; f = (lambda () stream)
  ; a = (answer) | package
  ; ss = [cache ansv* f] - suspended stream from table
  ; w = (ss ss ...)

  (define-syntax case-inf
    (syntax-rules ()
      ((_ e (() e0) ((f^) e1) ((w) ew) ((a^) e2) ((a f) e3))
       (let ((a-inf e))
         (cond
           ((not a-inf) e0)
           ((procedure? a-inf) (let ((f^ a-inf)) e1))
           ((and (pair? a-inf) (procedure? (cdr a-inf)))
            (let ((a (car a-inf)) (f (cdr a-inf))) e3))
           ((w? a-inf) (w-check a-inf
                         (lambda (f^) e1)
                         (lambda () (let ((w a-inf)) ew))))
           (else (let ((a^ a-inf)) e2)))))))

  (define ss-ready? (lambda (ss) (not (eq? (cache-ansv* (ss-cache ss)) (ss-ansv* ss)))))

  (define w? (lambda (w) (and (pair? w) (ss? (car w)))))

  (define w-check
    (lambda (ls sk fk)
      (let rec ((ls ls) (a '()))
        (cond
          ((null? ls) (fk))
          ((ss-ready? (car ls))
           (sk (lambdaf@ ()
                 (let ((f (ss-f (car ls)))
                       (ls `(,@(reverse a) . ,(cdr ls))))
                   (if (null? ls) (f)
                     (mplus (f) (lambdaf@ () ls)))))))
          (else (rec (cdr ls) `(,(car ls) . ,a)))))))

  (define taker
    (lambda (f st)
      (case-inf (f)
        (() '())
        ((f) (taker f st))
        ((w) '())
        ((a) `(,(car a) . ,(st (lambdaf@ () #f))))
        ((a f) `(,(car a) . ,(st f))))))

  (define (take n) (lambda (f) (if (zero? n) '() (taker f (take (- n 1))))))
  (define take* (lambda (f) (taker f take*)))
  (define take+ (lambda (f) (taker f (lambda (f) (lambda () (take+ f))))))
  (define-syntax run* (syntax-rules () ((_ (x) g ...) (run #f (x) g ...))))
  (define-syntax run+ (syntax-rules () ((_ (x) g ...) (run #t (x) g ...))))

  (define (make-== ext-s)
    (lambda (u v)
      (lambdag@ (s)
        ((unify ext-s) u v s))))

  (define ==-check (make-== ext-s-check))
  (define ==-no-check (make-== ext-s-no-check))
  (define == ==-check)

  (define-syntax exist
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambdag@ (s)
         (lambdaf@ ()
           (let ((x (make-var 'x s)) ...)
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
      ((_ a-inf g g* ...) (bind* (bind a-inf g) g* ...))))

  (define bind
    (lambda (a-inf g)
      (case-inf a-inf
        (() #f)
        ((f) (lambdaf@ () (bind (f) g)))
        ((w) (map (lambda (ss)
                    (make-ss (ss-cache ss) (ss-ansv* ss)
                      (lambdaf@ () (bind ((ss-f ss)) g))))
               w))
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
        ((w) (lambdaf@ () (let ((a-inf (f)))
                            (if (w? a-inf)
                              `(,@a-inf ,@w)
                              (mplus a-inf (lambdaf@ () w))))))
        ((a) `(,a . ,f))
        ((a f^) `(,a . ,(lambdaf@ () (mplus (f) f^)))))))

  (define-syntax project 
    (syntax-rules ()
      ((_ (x ...) e ... g)
       (lambdag@ (s)
         (let ((x ((walk* walk) x s)) ...)
           e ... (g s)))))))
