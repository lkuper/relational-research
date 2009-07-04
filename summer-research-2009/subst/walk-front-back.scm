  (define walk-fb
    (lambda (v s^)
      (inc-ws-calls s^)
      (call/cc
       (lambda (k)
         (let loop ((s s^))
           (inc-ws-steps)
           (cond
             ((var? v)
              (cond
                ((null? s) v) ;; XXX
                ((eq? s (vector-ref v 0)) (k v))
                ((eq? v (rhs (car s))) (k v))
                ((eq? v (lhs (car s))) (rhs (car s)))
                (else
                 (let ([v (loop (cdr s))])
                   (inc-ws-steps)
                   (ws-found-match)
                   (cond
                     ((var? v)
                      (cond
                        ((eq? v (lhs (car s))) (rhs (car s)))
                        (else v)))
                     (else (k v)))))))
             (else (k v))))))))
