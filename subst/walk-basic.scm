(define walk-basic
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ((s s^))
      (cond
        ((or (not (var? v)) (null? s)) v)
        ((eq? v (lhs (car s))) (begin (inc-ws-recrs)
                                      (ws-found-match)
                                      (walk-basic (rhs (car s)) s^)))
        (else (loop (cdr s)))))))
