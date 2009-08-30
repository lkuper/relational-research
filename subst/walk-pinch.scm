  (define walk-pinch-s
    (lambda (v s^)
      (inc-ws-calls s^)
      (let loop ((s s^) (s< '()))
        (inc-ws-steps)
        (cond
          ((var? v)
           (cond
             ((null? s) v) ;; XXX
             ((eq? s (var-birth v)) v)
             ((eq? v (rhs (car s))) v)
             ((eq? v (lhs (car s))) (pinch-s (rhs (car s)) s^ s<))
             (else (loop (cdr s) (cons (car s) s<)))))
          (else v)))))
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
          ((null? s<) v)
          ((var? v)
           (cond
             ;; ->
             ((eq? s> (var-value v)) v)
             ((eq? v (rhs (car s>))) v)
             ((eq? v (lhs (car s>))) (pinch-s (rhs (car s>)) s>^ (pinch-s-find (car s>) s<)))
             ;; <-
             ((eq? v (lhs (car s<))) (pinch-s (rhs (car s<)) s>^ (cdr s<)))
             (else (loop (cdr s>) (cdr s<)))))
          (else v)))))

