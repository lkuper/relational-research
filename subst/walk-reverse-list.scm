  (define walk-no-rec-stk
    (lambda (v s^)
      (inc-ws-calls s^)
      (let loop ([s s^] [s< '()])
        (inc-ws-steps)
        (cond
          ((var? v)
           (cond
             ((null? s) v) ;; XXX
             ((eq? s (var-value v)) v)
             ((eq? v (rhs (car s))) v)
             ((eq? v (lhs (car s))) (walk-no-rec-stk-back (rhs (car s)) s<))
             ;;((eq? v (lhs (car s))) (if (null? s<) (rhs (car s)) (walk-no-rec-stk-back (rhs
             (else (loop (cdr s) (cons (car s) s<)))))
          (else v)))))
  (define walk-no-rec-stk-back
    (lambda (v s)
      (ws-found-match)
      (inc-ws-steps)
      (cond
        ((var? v)
         (cond
           ((null? s) v) ;; why do we need this?
           ((eq? v (lhs (car s))) (walk-no-rec-stk-back (rhs (car s)) (cdr s)))
           (else (walk-no-rec-stk-back v (cdr s)))))
        (else v))))

