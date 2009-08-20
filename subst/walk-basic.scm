(define-syntax rhs
  (syntax-rules ()
    ((_ x) (cdr x))))
(define-syntax lhs
  (syntax-rules ()
    ((_ x) (car x))))
(define walk-basic
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ((s s^))
      (inc-ws-steps)
      (cond
        ((var? v)
         (cond
           ((null? s) v)
           ((eq? v (lhs (car s))) (begin (inc-ws-recrs)
                                         (ws-found-match)
                                         (walk-basic (rhs (car s)) s^)))
           (else (loop (cdr s)))))
        (else v)))))
