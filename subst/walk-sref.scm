(define var-birth
  (lambda (x)
    (vector-ref x 0)))

(define walk-sref
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ((s s^))
      (inc-ws-steps)
      (cond
        ((or (not (var? v))
             (null? s)
             (eq? s (var-birth v))
             (eq? v (rhs (car s))))
         v) 
        ((eq? v (lhs (car s))) (step (rhs (car s)) s^))
        (else (loop (cdr s)))))))

(define step
  (lambda (v s^)
    (inc-ws-recrs)
    (ws-found-match)
    (let loop ((s s^))
      (inc-ws-steps)
      (cond
        ((or (not (var? v)) (eq? v (rhs (car s)))) v)
        ((eq? v (lhs (car s))) (step (rhs (car s)) s^))
        (else (loop (cdr s)))))))
