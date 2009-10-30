(define walk-fb
  (lambda (v s^)
    (inc-ws-calls s^)
    (call/cc
     (lambda (k)
       (let loop ((s s^))
         (inc-ws-steps)
         (cond
           ((or (not (var? v))
                (null? s)
                (eq? s (var-birth v))
                (eq? v (rhs (car s)))) (k v))
           ((eq? v (lhs (car s))) (rhs (car s)))
           (else
            (let ([v (loop (cdr s))])
              (inc-ws-steps)
              (ws-found-match)
              (cond
                [(not (var? v)) (k v)]
                [(eq? v (lhs (car s))) (rhs (car s))]
                [else v])))))))))
