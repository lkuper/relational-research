; binary random access list based on skew numbers
(module skew-bral-def
  (kd:empty kd:size kd:associate kd:lookup kd:update kd:get-value kd:reserve)
  ;(import (rnrs) (rnrs records syntactic) (ikarus) (match))
  (import (scheme))

  ;(define-record-type bral (fields (mutable size) realized ls))
  ;(define-record bral ((mutable unsigned-32 size)
                       ;(immutable integer-32 realized)
                       ;(immutable ls)))
  (define-syntax make-bral
    (syntax-rules ()
      [(_ size realized ls) `(,size . (,realized . ,ls))]))
  (define bral-size car)
  (define set-bral-size! set-car!)
  (define bral-realized cadr)
  (define bral-ls cddr)

  ;(define-record-type node (fields val even odd))
  (define-record node ((immutable val)
                       (immutable even)
                       (immutable odd)))

  ; -- public 

  (define kd:empty
    (lambda ()
      (make-bral 0 -1 '())))

  (define kd:reserve
    (lambda (b)
      (let [(n (bral-size b))]
        (set-bral-size! b (fx+ 1 n))
        n)))
      ;(make-bral (fx+ 1 (bral-size b))  ; purely functional
                 ;(bral-realized b)
                 ;(bral-ls b))))

  (define kd:size
    (lambda (b)
      (bral-size b)))

  (define kd:associate
    (lambda (i v b)
      (if (fx> i (bral-realized b))
        (make-bral (bral-size b) i
                   (cons^ v (bral-ls b) (fx- i (bral-realized b))))
        (kd:update i v b))))

  (define kd:lookup
    (lambda (i b)
      (if (fx> i (bral-realized b)) #f
          (lookup (reverse-idx i b) (bral-ls b)))))

  (define kd:update
    (lambda (i v b)
      (make-bral (bral-size b)
                 (bral-realized b)
                 (update (reverse-idx i b) v (bral-ls b)))))

  (define kd:get-value
    (lambda (v)
      (cond
        [(node? v) (node-val v)]
        [else (car v)])))

  ; --- helpers

  (define br (vector 'br)) ; birth record

  (define reverse-idx
    (lambda (i b)
      (fx- (bral-realized b) i)))

  (define shift (lambda (n) (fxsra n 1)))

  (define cons^
    (lambda (v ls n)
      (let* [(v* (if (fx= 1 n) v br))
             (res (cond
                    [(and (pair? ls) (pair? (cdr ls)) (fx= (caar ls) (caadr ls)))
                     (cons `(,(fx+ 1 (fx+ (caar ls) (caadr ls)))
                              . ,(make-node v* (cdar ls) (cdadr ls))) (cddr ls))]
                    [else (cons `(1 . ,v*) ls)]))]
        (if (fx= 1 n) res (cons^ v res (fx- n 1))))))

  (define lookup-tree
    (lambda (w i t)
      (cond
        [(node? t)
         (if (fxzero? i) (if (eq? (node-val t) br) #f t)
             (let [(w/2 (shift w))]
               (if (fx<= i w/2)
                   (lookup-tree w/2 (fx- i 1) (node-even t))
                   (lookup-tree w/2 (fx- (fx- i 1) w/2) (node-odd t)))))]
        [else (if (fxzero? i)
                  (if (eq? t br) #f (cons t '()))
                  #f)])))

  (define lookup
    (lambda (i ls)
      (cond
        [(null? ls) #f]
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
        [else (if (fxzero? i) v (error 'update-tree "illegal index ~s" i))])))

  (define update
    (lambda (i v ls)
      (cond
        [(null? ls) (error 'k:update "illegal index ~s" i)]
        [else (let [(t (car ls))]
                (if (fx< i (car t))
                    (cons `(,(car t) . ,(update-tree (car t) i v (cdr t))) (cdr ls))
                    (cons t (update (fx- i (car t)) v (cdr ls)))))])))
  )
