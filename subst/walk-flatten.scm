(define walk-no-rec-stkf
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ([s s^] [s< '()])
      (inc-ws-steps)
      (cond
        ((or (not (var? v)) (null? s)
             (eq? s (var-birth v))
             (eq? v (rhs (car s))))
         (values v s^))
        ((eq? v (lhs (car s)))
         (walk-no-rec-stkf-back (rhs (car s)) `(,v) s^ s<))
        (else (loop (cdr s) (cons (car s) s<)))))))

(define walk-no-rec-stkf-back
  (lambda (v m s> s)
    (ws-found-match)
    (inc-ws-steps)
    (cond
      ((not (var? v)) (ret-no-rec-stkf v m s>))
      ((null? s) (values v s>)) ;; why do we need this?
      ((eq? v (lhs (car s)))
       (walk-no-rec-stkf-back (rhs (car s)) (cons v m) s> (cdr s)))
      (else (walk-no-rec-stkf-back v m s> (cdr s))))))

(define ret-no-rec-stkf
  (lambda (v m s)
    (let loop ([m m] [s s])
      (cond
        [(null? m) (values v s)]
        [else (loop (cdr m) (cons `(,(car m) . ,v) s))]))))


