(define walk-no-rec-stk
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ([s s^] [s< '()])
      (inc-ws-steps)
      (cond
        ((or (not (var? v))
             (null? s)
             (eq? s (var-birth v))
             (eq? v (rhs (car s)))) v)
        ((eq? v (lhs (car s))) (walk-no-rec-stk-back (rhs (car s)) s<))
        (else (loop (cdr s) (cons (car s) s<)))))))

(define walk-no-rec-stk-back
  (lambda (v s)
    (ws-found-match)
    (inc-ws-steps)
    (cond
      ((or (not (var? v) (null? s))) v)
      ((eq? v (lhs (car s))) (walk-no-rec-stk-back (rhs (car s)) (cdr s)))
      (else (walk-no-rec-stk-back v (cdr s))))))
