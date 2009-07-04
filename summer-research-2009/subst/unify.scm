  (define unify-sv
    (lambda (v w s)
      (let ((v (walk v s))
            (w (walk w s)))
        (cond
          ((eq? v w) s)
          ((var? v) (ext-s v w s))
          ;;((var? v) ;; ordering testing
          ;;(if (and (var? w)
          ;;(fx< (fxabs (fx- (var-idx w) (cadr s)))
          ;;(fxabs (fx- (var-idx v) (cadr s)))))
          ;;(ext-s w v s)
          ;;(ext-s v w s)))
          ((var? w) (ext-s w v s))
          ((and (pair? v) (pair? w))
           (let ((s (unify-sv (car v) (car w) s)))
             (and s (unify-sv (cdr v) (cdr w) s))))
          ((equal? v w) s)
          (else #f)))))
