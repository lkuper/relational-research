(module alphatap (do-prove-th A E copy-termo-k copy-termo-n copy-termo)
(import (mk) (settings))

;;(define var
;;  (lambda (n)
;;    (make-var n '())))

(define-syntax A
  (syntax-rules ()
    ((A var body) `(forall var ,(lambda (var) `body)))))

(define-syntax E
  (syntax-rules ()
    ((E var body) `(ex var ,(lambda (var) `body)))))

(define (show-formula fml)
  (cond
    ((not (pair? fml)) fml)
    ((eq? (car fml) 'var) fml)
    ((eq? (car fml) 'forall) (let ((var (cadr fml)))
			       `(A ,var ,(show-formula ((caddr fml) var)))))
    ((eq? (car fml) 'ex) (let ((var (cadr fml)))
			       `(E ,var ,(show-formula ((caddr fml) var)))))
    (else (cons (car fml) (map show-formula (cdr fml))))))

(define-syntax match-case-simple
  (syntax-rules ()
    ((_ exp clause ...)
      (let ((val-to-match exp))
	(match-case-simple* val-to-match clause ...)))))

(define (match-failure val)
  (error "failed match" val))

(define-syntax match-case-simple*
  (syntax-rules (else)
    ((_ val (else exp ...))
      (let () exp ...))
    ((_ val)
      (match-failure val))
    ((_ val (pattern () exp ...) . clauses)
      (let ((fail (lambda () (match-case-simple* val . clauses))))
	  ; note that match-pattern may do binding. Here,
	  ; other clauses are outside of these binding
	(match-pattern val pattern (let () exp ...) (fail))))
    ((_ val (pattern guard exp ...) . clauses)
      (let ((fail (lambda () (match-case-simple* val . clauses))))
	(match-pattern val pattern
	  (if guard (let () exp ...) (fail))
	  (fail))))
))


; (match-pattern val pattern kt kf)
(define-syntax match-pattern
  (syntax-rules (? quote unquote)
    ((_ val ? kt kf) kt)
    ((_ val () kt kf)
      (if (null? val) kt kf))
    ((_ val (quote lit) kt kf)
      (if (equal? val (quote lit)) kt kf))
    ((_ val (unquote var) kt kf)
      (let ((var val)) kt))
    ((_ val (x . y) kt kf)
      (if (pair? val)
	(let ((valx (car val))
	      (valy (cdr val)))
	  (match-pattern valx x
	    (match-pattern valy y kt kf)
	    kf))
	kf))
    ((_ val lit kt kf)
      (if (equal? val (quote lit)) kt kf))))

;(define (nnf fml)
(define (nnf fml s)
  (match-case-simple fml

    ; trivial re-writing using the standard tautologies
    ((not (not ,a)) ()
      (nnf  a s))
    ((not (forall ,var ,gfml)) ()
      (nnf  `(ex ,var ,(lambda (x) `(not ,(gfml x)))) s))
    ((not (ex ,var ,gfml)) ()
      (nnf  `(forall ,var ,(lambda (x) `(not ,(gfml x)))) s))
    ((not (and . ,fmls)) ()
      (nnf  `(or ,@(map (lambda (x) `(not ,x)) fmls)) s))
    ((not (or . ,fmls)) ()
      (nnf  `(and ,@(map (lambda (x) `(not ,x)) fmls)) s))
    ((=> ,a ,b) ()
      (nnf  `(or (not ,a) ,b) s))
    ((not (=> ,a ,b)) ()
      (nnf  `(and ,a (not ,b)) s))
    ((<=> ,a ,b) ()
      (nnf  `(or (and ,a ,b) (and (not ,a) (not ,b))) s))
    ((not (<=> ,a ,b)) ()
      (nnf  `(or (and (not ,a) ,b) (and ,a (not ,b))) s))

    
    ; propagate inside
    ((forall ,x ,gfml) ()
     (let ((v (var x s))) ; DCB
       `(forall ,v ,(nnf (gfml v) s))))
    ((and . ,fmls) ()
      `(and ,@(map (lambda (x) (nnf  x s)) fmls)))
    ((or . ,fmls) ()
      `(or ,@(map (lambda (x) (nnf  x s)) fmls)))

    ; skolemization. See the paper
    ((ex ,v ,gfml) ()
     (let* ((fvars (rem-dups (fv (show-formula `(ex ,v ,gfml)))))
            (fml-ex `(,(gensym) . ,fvars))
            (fml-sk (gfml fml-ex)))
       (nnf  fml-sk s)))
    ((ex ? ,gfml) ()
	     ; replace quantified var with a constant. We use `sk' for clarity
      (let* ((fml-ex `(sk ,(show-formula (gfml 'ex))))
	     (fml-sk (gfml fml-ex))) ; replace qu. var. with skolem function
	(nnf  fml-sk s)))

    ; handle literals
    (else fml)))

(define fv
  (lambda (fml)
    (match-case-simple fml
      [,x (var? x) (list x)]
      [(not ,x) () (fv x)]
      [(,op ,x ,y) (member op '(and or => <=>)) (append (fv x) (fv y))]
      [(forall ,x ,t) () (remq x (fv t))]
      [(exist ,x ,t) () (remq x (fv t))]
      [(,f . ,args) () (apply append (map fvt args))]
      [else '()])))

(define fvt
  (lambda (fml)
    (match-case-simple fml
      [,x (var? x) (list x)]
      [(,f . ,args) () (apply append (map fvt args))]
      [else '()])))

(define rem-dups
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [(member (car ls) (cdr ls)) (rem-dups (cdr ls))]
      [else (cons (car ls) (rem-dups (cdr ls)))])))


;(define proveo
  ;(lambda (fml unexp lits freev)
    ;(conda
      ;((exist (a b)
         ;(== `(and ,a ,b) fml)
         ;(proveo a (cons b unexp) lits freev)))
      ;((exist (a b)
         ;(== `(or ,a ,b) fml)
         ;(proveo a unexp lits freev)
         ;(proveo b unexp lits freev)))
      ;((exist (x x1 b b1 unexp1)
         ;(== `(forall ,x ,b) fml)
         ;(copy-termo `(,x ,b ,freev) `(,x1 ,b1 ,freev))
         ;(appendo unexp (list fml) unexp1)
         ;(proveo b1 unexp1 lits (cons x1 freev))))
      ;((conde
         ;((exist (l rest neg)
            ;(== `(,l . ,rest) lits)
            ;(conda
              ;((== `(not ,neg) fml)) ((== `(not ,fml) neg)))
            ;(conde
              ;((==-check neg l))
              ;((proveo fml '() rest freev)))))
         ;((exist (next unexp1)
            ;(== `(,next . ,unexp1) unexp)
            ;(proveo next unexp1 (cons fml lits) freev))))))))

(define membero
  (lambda (x ls)
    (conde
      ((exist (d)
         (==-check `(,x . ,d) ls)))
      ((exist (a d)
         (== `(,a . ,d) ls)
         (membero x d))))))

(define appendo 
  (lambda (l1 l2 l3)
    (conde
      ((== l1 '()) (== l2 l3))
      ((exist (x l11 l31)
         (== l1 (cons x l11))
         (== l3 (cons x l31))
         (appendo l11 l2 l31))))))


(define proveo
  (lambda (fml unexp lits freev)
    (conda
      ((exist (a b)
         (== `(and ,a ,b) fml)
         (proveo a (cons b unexp) lits freev)))
      ((exist (a b)
         (== `(or ,a ,b) fml)
         (proveo a unexp lits freev)
         (proveo b unexp lits freev)))
      ;((exist (x x1 b b1 unexp1)
      ((exist (x b x1 b1 unexp1)
         (== `(forall ,x ,b) fml)
         (copy-termo `(,x ,b ,freev) `(,x1 ,b1 ,freev))
         (appendo unexp (list fml) unexp1)
         (proveo b1 unexp1 lits (cons x1 freev))))
      ((conde
         ;((exist (l rest neg)
         ((exist (neg)
            (conda
              ((== `(not ,neg) fml)) ((== `(not ,fml) neg)))
            (membero neg lits)))
         ((exist (next unexp1)
            (== `(,next . ,unexp1) unexp)
            (proveo next unexp1 (cons fml lits) freev))))))))


(define (do-prove-th axioms theorem)
  (let ((pr (run 1 (q)
              (lambdag@ (s)
                (let* ((nf (prepare axioms theorem s)))
                  ((proveo nf '() '() '())
                   s))))))
    (if (null? pr) (error 'prove "failure!"))
    pr))

;(define (do-prove-th axioms theorem)
;  (let* ((nf (prepare axioms theorem)))
;    (let ((pr (run 1 (q) (proveo nf '() '() '()))))
;      (if (null? pr) (error 'prove "failure!"))
;      pr)))

; (define (do-prove-th axioms theorem)
; ;  (printf "Axioms: ")
; ;  (map (lambda (x) (printf "~s " (show-formula x))) axioms)
; ;  (newline)
; ;  (printf "Theorem: ~s\n" (show-formula theorem))
;   (let* ((nf (prepare axioms theorem)))
; ;    (printf "NNF is: \n")
; ;    (pretty-print nf) (newline)
;     (let ((pr (run 1 (q) (proveo nf '() '() '()))))
;       (if (null? pr) (error 'prove "failure!"))
; ;      (printf "The proof is: \n")
; ;      (pretty-print pr)
; ;      (newline)(newline)
;       pr)))

(define build-and
  (lambda (ax)
    (cond
      [(null? ax) '()]
      [(null? (cdr ax)) (car ax)]
      [else `(and ,(car ax) ,(build-and (cdr ax)))])))




(define (do-prove-th-with-proof axioms theorem proof)
;  (printf "Axioms: ")
;  (map (lambda (x) (printf "~s " (show-formula x))) axioms)
;  (newline)
;  (printf "Theorem: ~s\n" (show-formula theorem))
  (let* ((nf (prepare axioms theorem)))
;    (printf "NNF is: ~s\n" nf)
    (let ((pr (time (run 1 (q) (proveo nf '() '() '() proof)))))
      (if (null? pr) (error 'prove "failure!"))
;      (printf "The proof is: ~s\n\n" pr)
      )))

(define prepare
  ;(lambda (axioms theorem)
  (lambda (axioms theorem s)
    (let* ((neg-formula (if (null? axioms)
                            `(not ,theorem)
                            (build-and (cons `(not ,theorem) axioms))))
           (nf (nnf neg-formula s)))
           ;(nf (nnf neg-formula)))
      nf)))

;; -- copy-term

(define copy-walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (copy-walk (cdr a) s))
           (else v))))
      (else v))))

(define copy-walk*
  (lambda (w s)
    (let ((v (copy-walk w s)))
      (cond
        ;((var? v) v)
        ((pair? v)
         (cons
           (copy-walk* (car v) s)
           (copy-walk* (cdr v) s)))
        (else v)))))

; -- normal
(define refresh-s-n
  (lambda (v s)
    (let ((v (copy-walk v s)))
      (cond
        ((var? v)
         (cons (cons v (var 'copy 'ignore)) s))
        ((pair? v) (refresh-s-n (cdr v)
                     (refresh-s-n (car v) s)))
        (else s)))))

(define copy-termo-n
  (lambda (t1 t2)
    (project (t1)
      (== (copy-walk* t1 (refresh-s-n t1 '())) t2))))

; -- skew
(define refresh-s-k
  (lambda (v s)
    (let ((v (copy-walk v (cdr s))))
      (cond
        ((var? v)
         (let ([vc (var 'copy 'ignore)])
           (cons
             (ext-s-init vc vc (car s))
             (cons (cons v vc) (cdr s)))))
        ((pair? v) (refresh-s-k (cdr v)
                     (refresh-s-k (car v) s)))
        (else s)))))

(define copy-termo-k
  (lambda (t1 t2)
    (lambdag@ (s)
      (let* ([t1 (walk* t1 s)]
             [s^ (refresh-s-k t1 (cons s '()))])
        (unify (copy-walk* t1 (cdr s^)) t2 (car s^))))))

; -- skew-def
(define refresh-s-kd
  (lambda (v s)
    (let ((v (copy-walk v (cdr s))))
      (cond
        ((var? v)
         (let ([vc (var 'copy (car s))])
           (cons
             (car s)
             (cons (cons v vc) (cdr s)))))
        ((pair? v) (refresh-s-kd (cdr v)
                     (refresh-s-kd (car v) s)))
        (else s)))))

(define copy-termo-kd
  (lambda (t1 t2)
    (lambdag@ (s)
      (let* ([t1 (walk* t1 s)]
             [s^ (refresh-s-kd t1 (cons s '()))])
        (unify (copy-walk* t1 (cdr s^)) t2 (car s^))))))


; -- choose copy-termo
(define-syntax copy-termo
  (syntax-rules ()
    [(_ t1 t2) ((choose-copy-term copy-termo-n
                                  copy-termo-k
                                  copy-termo-kd) t1 t2)]))


(define var-name
  (lambda (v)
    (vector-ref v 0)))
)
