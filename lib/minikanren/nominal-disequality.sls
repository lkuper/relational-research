(library (minikanren nominal-disequality)
  (export run run* run+ conde exist fresh hash =/= == ==-check (rename (make-tie tie)))
  (import (rnrs))

  (define-syntax lambdaf@ (syntax-rules () ((_ () e) (lambda () e))))
  (define-syntax lambdag@ (syntax-rules () ((_ (p) e) (lambda (p) e))))

  (define-record-type sus (fields pi (immutable v %sus-v)))
  (define sus-v (lambda (s) (or (%sus-v s) s)))
  (define-record-type var (parent sus) (fields n))
  (define-record-type nom (fields n))
  (define-record-type tie (fields a t))

  ; v means var, x means sus, a means nom
  ; s  :: ((v . t) ...)
  ; h* :: ((a . v) ...)
  ; c* :: ((s . h*) ...)

  (define-record-type p (fields s h* c*))
  (define p/s (lambda (p s) (make-p s (p-h* p) (p-c* p))))
  (define p/h* (lambda (p h*) (make-p (p-s p) h* (p-c* p))))
  (define p/c* (lambda (p c*) (make-p (p-s p) (p-h* p) c*)))
  (define empty-p (make-p '() '() '()))
  (define c-s (lambda (c) (car c)))
  (define c-h* (lambda (c) (cdr c)))
  (define make-c (lambda (s h*) `(,s . ,h*)))

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
        (lambdaf@ () ((exist (q) g g* ... (reify q)) empty-p))))))

  (define taker
    (lambda (f st)
      (case-inf (f)
        (() '())
        ((f) (taker f st))
        ((a) `(,(car a) . ,(st (lambdaf@ () #f))))
        ((a f) `(,(car a) . ,(st f))))))

  (define (take n) (lambda (f) (if (zero? n) '() (taker f (take (- n 1))))))
  (define take* (lambda (f) (taker f take*)))
  (define-syntax run* (syntax-rules () ((_ (x) g ...) (run #f (x) g ...))))
  (define take+ (lambda (f) (taker f (lambda (f) (lambda () (take+ f))))))
  (define-syntax run+ (syntax-rules () ((_ (x) g ...) (run #t (x) g ...))))

  (define apply-pi
    (lambda (pi t)
      (let rec ((t t))
        (cond
          ((nom? t) (api pi t))
          ((and (var? t) (null? pi)) t) ; for reification
          ((sus? t) (make-sus (compose-pis pi (sus-pi t)) (sus-v t)))
          ((tie? t) (make-tie (api pi (tie-a t)) (rec (tie-t t))))
          ((pair? t) `(,(rec (car t)) . ,(rec (cdr t))))
          (else t)))))

  (define api
    (lambda (pi a)
      (fold-right
        (lambda (swap a)
          (cond
            ((eq? a (car swap)) (cdr swap))
            ((eq? a (cdr swap)) (car swap))
            (else a)))
        a pi)))

  (define disagreement-set
    (lambda (pi1 pi2)
      (let* ((i (lambda (a a*)
                  (if (or (memq a a*)
                        (eq? (api pi1 a) (api pi2 a)))
                    a* `(,a . ,a*))))
             (c (lambda (pi a*)
                  (fold-left
                    (lambda (a* swap)
                      (i (car swap) (i (cdr swap) a*)))
                    a* pi))))
        (c pi1 (c pi2 '())))))

  (define compose-pis append)
  (define invert-pi reverse)

  (define s-extension
    (lambda (s^ s)
      (if (eq? s^ s) '()
        `(,(car s^) . ,(s-extension (cdr s^) s)))))

  (define h*-extension
    (lambda (h*^ h*)
      (cond
        ((null? h*^) '())
        ((member (car h*^) h*) (h*-extension (cdr h*^) h*))
        (else `(,(car h*^) . ,(h*-extension (cdr h*^) h*))))))

  (define h*-union
    (lambda (h*1 h*2)
      `(,@(h*-extension h*1 h*2) ,@h*2)))

  (define ==
    (lambda (u v)
      (lambdag@ (p)
        (let ((p (nominal-unify u v p)))
          (and p (let ((c* (verify-c* p)))
                   (and c* (p/c* p c*))))))))

  (define nominal-unify
    (lambda (u v p)
      (let ((p (unify u v p)))
        (and p (let ((h* (verify-h* (p-h* p) (p-s p))))
                 (and h* (p/h* p h*)))))))

  (define ==-check ==)

  (define =/=
    (lambda (u v)
      (lambdag@ (p)
        (cond
          ((nominal-unify u v p)
           => (lambda (!p)
                (let ((!s (s-extension (p-s !p) (p-s p)))
                      (!h* (h*-extension (p-h* !p) (p-h* p))))
                  (and
                    (or (pair? !s) (pair? !h*))
                    (p/c* p `(,(make-c !s !h*) . ,(p-c* p)))))))
          (else p)))))

  (define hash
    (lambda (a t)
      (lambdag@ (p)
        (let ((h* (do-hash a t (p-s p) (p-h* p))))
          (and h* (p/h* p h*))))))

  (define do-hash
    (lambda (a t s h*)
      (let rec ((t t) (h* h*)) 
        (let ((t (walk t s)))
          (cond
            ((eq? a t) #f)
            ((sus? t)
             (let ((a (apply-pi (invert-pi (sus-pi t)) a)))
               (ext-h* a (sus-v t) h*)))
            ((and (tie? t) (not (eq? a (tie-a t))))
             (rec (tie-t t) h*))
            ((pair? t)
             (let ((h* (rec (car t) h*)))
               (and h* (rec (cdr t) h*))))
            (else h*))))))

  (define verify-h* 
    (lambda (h* s)
      (let rec ((h* h*) (ac '()))
        (if (null? h*) ac
          (let ((ac (do-hash (caar h*) (cdar h*) s ac)))
            (and ac (rec (cdr h*) ac)))))))

  (define verify-c*
    (lambda (p)
      (let rec ((c* (p-c* p)))
        (cond
          ((null? c*) '())
          ((unify-c (car c*) p)
           => (lambda (p^)
                (let ((!s^ (s-extension (p-s p^) (p-s p)))
                      (!h*^ (verify-h*
                              (h*-union
                                (h*-extension (p-h* p^) (p-h* p))
                                (c-h* (car c*)))
                              (p-s p))))
                  (and !h*^
                    (or (pair? !s^) (pair? !h*^))
                    `(,(make-c !s^ !h*^) .
                      ,(rec (cdr c*)))))))
          (else (rec (cdr c*)))))))

  (define unify-c
    (lambda (c p)
      (let rec ((!s (c-s c)) (p p))
        (if (null? !s) p
          (let ((p (nominal-unify (caar !s) (cdar !s) p)))
            (and p (rec (cdr !s) p)))))))

  (define walk
    (lambda (t s)
      (let rec ((t t) (pi '()))
        (cond
          ((and (sus? t) (assq (sus-v t) s))
           => (lambda (p) (rec (cdr p) (compose-pis (sus-pi t) pi))))
          (else (apply-pi pi t))))))

  (define ext-s-check
    (lambda (v t p)
      (let ((s (p-s p)))
        (and (not (occurs? v t s))
          (p/s p (cons `(,v . ,t) s))))))

  (define tie-t* (lambda (t) (if (tie? t) (tie-t* (tie-t t)) t)))

  (define occurs?
    (lambda (v t s)
      (let rec ((t t))
        (let ((t (walk (tie-t* t) s)))
          (cond
            ((sus? t) (eq? v (sus-v t)))
            ((pair? t) (or (rec (car t)) (rec (cdr t))))
            (else #f))))))

  (define ext-h*
    (lambda (a v h*)
      (let ((h `(,a . ,v)))
        (if (member h h*) h* `(,h . ,h*)))))

  (define unify
    (lambda (u v p)
      (let* ((s (p-s p)) (h* (p-h* p))
             (u (walk u s)) (v (walk v s)))
        (cond
          ((eq? u v) p)
          ((and (sus? u) (sus? v) (eq? (sus-v u) (sus-v v)))
           (unify=sus (disagreement-set (sus-pi u) (sus-pi v)) (sus-v u) p))
          ((sus? u) (ext-s-check (sus-v u) (apply-pi (invert-pi (sus-pi u)) v) p))
          ((sus? v) (ext-s-check (sus-v v) (apply-pi (invert-pi (sus-pi v)) u) p))
          ((and (tie? u) (tie? v))
           (unify-ties (tie-a u) (tie-a v) (tie-t u) (tie-t v) p))
          ((and (pair? u) (pair? v))
           (let ((p (unify (car u) (car v) p)))
             (and p (unify (cdr u) (cdr v) p))))
          ((equal? u v) p)
          (else #f)))))

  (define unify=sus
    (lambda (a* v p)
      (let rec ((a* a*) (h* (p-h* p)))
        (if (null? a*) (p/h* p h*)
          (let ((h* (do-hash (car a*) v (p-s p) h*)))
            (and h* (rec (cdr a*) h*)))))))

  (define unify-ties
    (lambda (au av tu tv p)
      (if (eq? au av) (unify tu tv p)
        (let ((h* (do-hash au tv (p-s p) (p-h* p))))
          (and h* (unify tu (apply-pi `((,au . ,av)) tv)
                    (p/h* p h*)))))))

  (define-syntax fresh
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambdag@ (p)
         (lambdaf@ ()
           (let ((x (make-nom 'x)) ...)
             ((conde (g g* ...)) p)))))))

  (define-syntax exist
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambdag@ (p)
         (lambdaf@ ()
           (let ((x (make-var '() #f 'x)) ...)
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
      ((_ e) e)
      ((_ e g g* ...) (bind* (bind e g) g* ...))))

  (define bind
    (lambda (a-inf g)
      (case-inf a-inf
        (() #f)
        ((f) (lambdaf@ () (bind (f) g)))
        ((a) (g a))
        ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

  (define-syntax mplus*
    (syntax-rules ()
      ((_ e) e)
      ((_ e e* ...)
       (mplus e (lambdaf@ () (mplus* e* ...))))))

  (define mplus
    (lambda (a-inf f)
      (case-inf a-inf
        (() (f))
        ((f^) (lambdaf@ () (mplus (f) f^)))
        ((a) `(,a . ,f))
        ((a f^) `(,a . ,(lambdaf@ () (mplus (f) f^)))))))

  ; reification needs to be replaced by something more like the "rak" reifier

  (define purify-c*
    (lambda (c* s)
      (define ground?
        (lambda (t)
          (cond
            ((sus? t) (not (sus? (walk t s))))
            ((tie? t) (ground? (tie-t t)))
            ((pair? t) (and
                         (ground? (car t))
                         (ground? (cdr t))))
            (else #t))))
      (filter ground? c*)))

  (define remove-subsumed-c*
    (lambda (c*)
      (let rec ((c* c*) (a '()))
        (cond
          ((null? c*) a)
          ((let* ((c (car c*))
                  (p (make-p (c-s c) (c-h* c) '())))
             (or
               (subsumed-c*? p (cdr c*))
               (subsumed-c*? p a)))
           (rec (cdr c*) a))
          (else (rec (cdr c*) `(,(car c*) . ,a)))))))

  ; want to know whether c is unnecessary given c*
  ; c contains bindings and freshness constraints that should never be simultaneously all satisfied.
  ; if there is a c1 in c* such that
  ;   if you assume c's contents are satisfied
  ;   then c1's contents are also satisfied
  ; then c is unnecessary given c*
  ; because:
  ; c1 has some subsets of c's bindings and freshnesses
  ; so asserting that c1 should not be satisfied implies c should not be satisfied
  ; (c sat => c1 sat) => (c1 not sat => c not sat)

  (define subsumed-c*?
    (lambda (p c*)
      (and (pair? c*)
        (or (let ((p^ (unify-c (car c*) p)))
              (and p^
                (eq? (p-s p^) (p-s p))
                (null? (h*-extension (p-h* p^) (p-h* p)))))
          (subsumed-c*? p (cdr c*))))))

  (define strip-c*
    (lambda (c*)
      (fold-right
        (lambda (c c*)
          (let ((s (c-s c)) (h* (c-h* c)))
            (cond
              ((and (null? s) (null? h*)) c*)
              ((null? s) `((hash . ,h*) . ,c*))
              ((null? h*) `(,s . ,c*))
              (else `((,s (hash . ,h*)) . ,c*)))))
        '() c*)))

  (define rwalk
    (lambda (t s)
      (let rec ((t t) (pi '()))
        (cond
          ((and (sus? t) (assq (sus-v t) s))
           => (lambda (p) (rec (cdr p) (compose-pis (sus-pi t) pi))))
          ((and (nom? t) (assq t s))
           => (lambda (p) (rec (cdr p) pi)))
          (else (apply-pi pi t))))))

  (define walk*
    (lambda (w s)
      (let ((t (rwalk w s)))
        (cond
          ((tie? t)
           `(tie ,(rwalk (tie-a t) s) ,(walk* (tie-t t) s)))
          ((and (sus? t) (not (null? (sus-pi t))))
           `(sus ,(walk* (sus-pi t) s) ,(rwalk (sus-v t) s)))
          ((pair? t)
           `(,(walk* (car t) s) .
             ,(walk* (cdr t) s)))
          (else t)))))

  (define reify-var
    (lambda (n) (string->symbol (string-append "_." (number->string n)))))

  (define reify-nom
    (lambda (n) (string->symbol (string-append "a." (number->string n)))))

  (define reifying-s
    (lambda (t)
      (define make-counter (lambda () (let ((n 0)) (lambda () (let ((r n)) (set! n (+ n 1)) r)))))
      (let ((vc (make-counter)) (nc (make-counter)))
        (let rec ((t t) (s '()))
          (cond
            ((and (sus? t) (not (assq (sus-v t) s)))
             `((,(sus-v t) . ,(reify-var (vc))) . ,s))
            ((and (nom? t) (not (assq t s)))
             `((,t . ,(reify-nom (nc))) . ,s))
            ((tie? t) (rec (tie-t t) (rec (tie-a t) s)))
            ((pair? t) (rec (cdr t) (rec (car t) s)))
            (else s))))))

  (define reify
    (lambda (v)
      (lambda (p)
        (let ((v (walk* v (p-s p))))
          (let ((r (reifying-s v)))
            (let ((v (walk* v r))
                  (h* (reify-h* (p-h* p) r))
                  (c* (strip-c*
                        (walk*
                          (remove-subsumed-c*
                            ; INCORRECT TYPES
                            ; walk* takes a term
                            ; but a c* is not a term
                            ; because it contains vars
                            (purify-c* (walk* (p-c* p) (p-s p))
                              r))
                          r))))
              `(,(if (or (pair? h*) (pair? c*))
                   `(,v
                     ,@(if (pair? h*) `((hash . ,h*)) '())
                     ,@(if (pair? c*) `((=/= . ,c*)) '()))
                   v))))))))

  (define reify-h*
    (lambda (h* s)
      (define ins
        (lambda (n v r)
          (let ((rn (rwalk n s)) (rv (rwalk v s)))
            (if (and (symbol? rn) (symbol? rv))
              (let rec ((r r))
                (if (null? r) `((,rn . (,rv)))
                  (if (eq? rn (caar r))
                    `((,rn . (,rv . ,(cdar r))) . ,(cdr r))
                    `(,(car r) . ,(rec (cdr r)))))) r))))
      (let rec ((h* h*) (r '()))
        (if (null? h*) (map
                         (lambda (h)
                           `(,(car h) .
                             ,(list-sort
                                (lambda (a b)
                                  (string<?
                                    (symbol->string a)
                                    (symbol->string b)))
                                (cdr h))))
                         r)
          (rec (cdr h*) (ins (caar h*) (cdar h*) r)))))))
(import (minikanren nominal-disequality))
