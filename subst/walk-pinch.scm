(define walk-pinch-s
  (lambda (v s^)
    (inc-ws-calls s^)
    (let loop ((s s^) (s< '()))
      (inc-ws-steps)
      (cond
        ((or (not (var? v))
             (null? s)
             (eq? s (var-birth v))
             (eq? v (rhs (car s)))) v)
        ((eq? v (lhs (car s))) (pinch-s (rhs (car s)) s^ s<))
        (else (loop (cdr s) (cons (car s) s<)))))))

(define pinch-s-find
  (lambda (e s)
    (cond
      [(eq? e (car s)) (cdr s)]
      [else (pinch-s-find e (cdr s))])))

(define pinch-s
  (lambda (v s>^ s<^)
    (ws-found-match)
    (let loop ((s> s>^) (s< s<^))
      (inc-ws-steps)
      (cond
        ((or (not (var? v))
             (null? s<)
             ;; ->
             (eq? s> (var-birth v))
             (eq? v (rhs (car s>)))) v)
        ((eq? v (lhs (car s>)))
         (pinch-s (rhs (car s>)) s>^ (pinch-s-find (car s>) s<)))
        ;; <-
        ((eq? v (lhs (car s<))) (pinch-s (rhs (car s<)) s>^ (cdr s<)))
        (else (loop (cdr s>) (cdr s<)))))))
