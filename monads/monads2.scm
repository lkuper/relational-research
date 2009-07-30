;;;; Here is the stuff on the Maybe monad.

;; data Maybe a = Nothing | Just a

;; instance Monad Maybe where
;;   unit = Just
;;   fail = Nothing
;;   Nothing >>= f = Nothing
;;   (Just x) >>= f = f x

;; instance MonadPlus Maybe where
;;   mzero = Nothing
;;   Nothing `mplus` x = x
;;   x `mplus` _ = x

(define Just
 (lambda (v)
   `(Just . ,v)))

(define Nothing
 (lambda ()
   `(Nothing)))

(define fail
 (lambda ()
   (Nothing)))

(define unit
 (lambda (v)
   (Just v)))

(define bind
 (lambda (c f)
   (case (car c)
     [(Nothing) c]
     [(Just) (f (cdr c))])))

(define assq8
 (lambda (al)
   (cond
     [(null? al) (fail)]
     [(eq? (caar al) 8) (unit (car al))]
     [else (bind (assq8 (cdr al)) (lambda (v) (unit v)))])))

;; Actually, we can eta out the (lambda (v) --), and because binding
;; anything with unit just results in that thing, the last line is
;; suddenly a lot simpler.
(define assq8
 (lambda (al)
   (cond
     [(null? al) (fail)]
     [(eq? (caar al) 8) (unit (car al))]
     [else (assq8 (cdr al))])))

(define assq*
  (lambda (v l)
    (cond
      [(null? l) (fail)]
      [(= (caar l) v) (unit (car l))]
      [else (bind (assq* v (cdr l)) (lambda (v) (unit v)))])))

(define mzero Nothing)

(define mplus
  (lambda (c1 c2)
    (case (car c1)
      ((Nothing) c2)
      ((Just) c1))))

(pretty-print
  (bind (mplus (assq8 '((7 . 1)))
               (assq8 '((8 . 2))))
        (lambda (a)
          (assq* (cdr a) '((1 . 10) (2 . 20))))))




