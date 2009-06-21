; binary random access list based on skew numbers
(module skew-bral
  (k:size k:associate k:lookup k:update k:get-value k:empty)
  ;(import (rnrs) (rnrs records syntactic) (ikarus) (match))
  (import scheme)

  ;(define-record-type node (fields val even odd))
  (define-record node (val even odd))

  ; -- public 

  (define k:empty
    (lambda ()
      '(0)))

  (define k:size
    (lambda (ls)
      (car ls)))

  (define k:associate
    (lambda (v ls)
      (cons (fx+ 1 (car ls)) (bind v (cdr ls)))))

  (define from-tail
    (lambda (i ls)
      (fx- (fx- (car ls) 1) i)))

  (define k:lookup
    (lambda (i ls)
      (lookup (from-tail i ls) (cdr ls))))

  (define k:update
    (lambda (i v ls)
      (cons (car ls) (update (from-tail i ls) v (cdr ls)))))

  (define k:get-value
    (lambda (v)
      (cond
        [(node? v) (node-val v)]
        [else (car v)])))

  ; --- helpers

  (define shift (lambda (n) (fxsra n 1)))

  ;(define bind ; DB - probably need to rewrite without match for speed
    ;(lambda (v ls)
      ;(match ls
        ;[((,w1 . ,t1) (,w2 . ,t2) . ,ls*)
         ;(if (fx= w1 w2)
           ;(cons `(,(fx+ 1 (fx+ w1 w2)) . ,(make-node v t1 t2)) ls*)
           ;(cons `(1 . ,v) ls))]
        ;[,ls (cons `(1 . ,v) ls)])))
  (define bind ; DB - probably need to rewrite without match for speed
    (lambda (v ls)
      (cond
        [(and (pair? ls) (pair? (cdr ls)) (fx= (caar ls) (caadr ls)))
         (cons `(,(fx+ 1 (fx+ (caar ls) (caadr ls)))
                  . ,(make-node v (cdar ls) (cdadr ls))) (cddr ls))]
        [else (cons `(1 . ,v) ls)])))

  (define lookup-tree
    (lambda (w i t)
      (cond
        [(node? t)
         (if (fxzero? i) t ;(node-val t)
             (let [(w/2 (shift w))]
               (if (fx<= i w/2)
                   (lookup-tree w/2 (fx- i 1) (node-even t))
                   (lookup-tree w/2 (fx- (fx- i 1) w/2) (node-odd t)))))]
        [else (if (fxzero? i) (cons t '()) #f)])))
        ;[else (if (fxzero? i) t (error 'lookup-tree "illegal index"))])))

  ;(define lookup   ; DB - too slow :(
    ;(lambda (i ls)
      ;(match ls
        ;[() (error 'k:lookup "illegal index")]
        ;[((,w . ,t) . ,ls*)
         ;(if (fx< i w)
             ;(lookup-tree w i t)
             ;(lookup (fx- i w) ls*))])))
  (define lookup
    (lambda (i ls)
      (cond
        [(null? ls) #f]
        ;[(null? ls) (error 'k:lookup "illegal index")]
        [else (let [(t (car ls))]
                (if (fx< i (car t))
                    (lookup-tree (car t) i (cdr t))
                    (lookup (fx- i (car t)) (cdr ls))))])))

  (define update-tree
    (lambda (w i v t)
      (cond
        [(node? t)
         (if (fxzero? i) (make-node v (node-even t) (node-odd t))
             (let [(w/2 (shift w))]
               (if (fx<= i w/2)
                   (make-node (node-val t)
                              (update-tree w/2 (fx- i 1) v (node-even t))
                              (node-odd t))
                   (make-node (node-val t)
                              (node-even t)
                              (update-tree w/2 (fx- (fx- i 1) w/2) v (node-odd t))))))]
        [else (if (fxzero? i) v (error 'update-tree "illegal index"))])))

  (define update
    (lambda (i v ls)
      (cond
        [(null? ls) (error 'k:update "illegal index ~s ~s" i v)]
        [else (let [(t (car ls))]
                (if (fx< i (car t))
                    (cons `(,(car t) . ,(update-tree (car t) i v (cdr t))) (cdr ls))
                    (cons t (update (fx- i (car t)) v (cdr ls)))))])))
  )
