  (define walk-sref
    (lambda (v s^)
      (inc-ws-calls s^)
      (let loop ((s s^))
        (inc-ws-steps)
        (cond
          ((var? v)
           (cond
             ((null? s) v) ;; XXX
             ((eq? s (vector-ref v 0)) v)
             ((eq? v (rhs (car s))) v)
             ((eq? v (lhs (car s))) (step (rhs (car s)) s^))
             (else (loop (cdr s)))))
          (else v)))))

  (define step
    (lambda (v s^)
      (inc-ws-recrs)
      (ws-found-match)
      (let loop ((s s^))
        (inc-ws-steps)
        (cond
          ((var? v)
           (cond
             ((eq? v (rhs (car s))) v)
             ((eq? v (lhs (car s))) (step (rhs (car s)) s^))
             (else (loop (cdr s)))))
          (else v)))))
