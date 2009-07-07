(define lengtho
  (lambda (ls out)
    (disj
      (conj (nullo ls) (== '() out))
      (let ((d (var 'd)) (res (var 'res)))
        (conj
          (cdro ls d)
          (conj
            (lengtho d res)
            (pluso res '(1) out)))))))

(test-check (run/1 #f (q) (lengtho '(a b c) q))
  (run/1 #f (q) (lengtho '(a b c) q))
  '((1 1)))

(test-check (run/1 #f (q) (lengtho '() q))
  (run/1 #f (q) (lengtho '() q))
  '(()))

(test-check (conj (lengtho ls out) (== `(,ls ,out) q))
  (run/1 5 (q)
    (let ((ls (var 'ls)) (out (var 'out)))
      (conj (lengtho ls out) (== `(,ls ,out) q))))
  '((() ())
    ((_.0) (1))
    ((_.0 _.1) (0 1))
    ((_.0 _.1 _.2) (1 1))
    ((_.0 _.1 _.2 _.3) (0 0 1))))

(test-divergence (run/1 #f (q) (lengtho q '(1 1)))
  (run/1 #f (q) (lengtho q '(1 1))))

(test-check (run/1 #f (q) (lengtho q '()))
  (run/1 #f (q) (lengtho q '()))
  '(()))

;;; swap the last two goals

(define lengtho
  (lambda (ls out)
    (disj
      (conj (nullo ls) (== '() out))
      (let ((d (var 'd)) (res (var 'res)))
        (conj
          (pluso res '(1) out)
          (conj
            (lengtho d res)
            (cdro ls d)))))))

(test-divergence (run/1 #f (q) (lengtho '(a b c) q))
  (run/1 #f (q) (lengtho '(a b c) q)))

(test-check (run/1 #f (q) (lengtho '() q))
  (run/1 #f (q) (lengtho '() q))
  '(()))

(test-check (conj (lengtho ls out) (== `(,ls ,out) q))
  (run/1 5 (q)
    (let ((ls (var 'ls)) (out (var 'out)))
      (conj (lengtho ls out) (== `(,ls ,out) q))))
  '((() ())
    ((_.0) (1))
    ((_.0 _.1) (0 1))
    ((_.0 _.1 _.2) (1 1))
    ((_.0 _.1 _.2 _.3) (0 0 1))))


(test-check (run/1 #f (q) (lengtho q '(1 1)))
  (run/1 #f (q) (lengtho q '(1 1)))
  '((_.0 _.1 _.2)))

(test-check (run/1 #f (q) (lengtho q '()))
  (run/1 #f (q) (lengtho q '()))
  '(()))


;;; play more games
(test-check (conj (== n m) (pluso n '(1) m))
  (run/1 1 (q)
    (let ((n (var 'n)) (m (var 'm)))
      (conj (pluso n '(1) m) (== n m))))
  '())

(test-check (conj (== n m) (pluso n '(1) m))
  (run/1 #f (q)
    (let ((n (var 'n)) (m (var 'm)))
      (conj (pluso n '(1) m) (== n m))))
  '())

(define foo
  (lambda ()
    (conj fail (foo))))

(test-check (run/1 #f (q) (foo))
  (run/1 #f (q) (foo))
  '())

(define bar
  (lambda ()
    (conj (bar) fail)))

(test-check (run/1 #f (q) (bar))
  (run/1 #f (q) (bar))
  '())

(define baz
  (lambda (z)
    (let ((x (var 'x)))
      (conj (pluso x '(1) z) (baz z)))))

(test-check (run/1 #f (q) (baz '()))
  (run/1 #f (q) (baz '()))
  '())

(define quuxw
  (lambda (z)
    (let ((x (var 'x)) (y (var 'y)))
      (conj (pluso x '(1) z) (quuxw y)))))

(test-check (run/1 #f (q) (quuxw '()))
  (run/1 #f (q) (quuxw '()))
  '())

(define bazzw
  (lambda (z)
    (let ((x (var 'x)))
      (conj (bazzw z) (pluso x '(1) z)))))

(test-check (run/1 #f (q) (bazzw '()))
  (run/1 #f (q) (bazzw '()))
  '())

(define blat
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj (cdro ls d) (conj (pluso res '(1) out) (blat d res))))))

(test-check (run/1 #f (q) (blat q '()))
  (run/1 #f (q) (blat q '()))
  '())

(define blazw
  (lambda (out)
    (let ((res (var 'res)))
      (conj (pluso res '(1) out) (blazw res)))))

(test-check (run/1 #f (q) (blazw '()))
  (run/1 #f (q) (blazw '()))
  '())

(define blazw
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj (blazw d res) (pluso res '(1) out)))))

(test-check (run/1 #f (q) (blazw q '()))
  (run/1 #f (q) (blazw q '()))
  '())

(define blazw
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj (blazw d res) (conj (pluso res '(1) out) (cdro ls d))))))

;;; Can the 'cdro; really be causing divergence????
(test-check (run/1 #f (q) (blazw q '()))
  (run/1 #f (q) (blazw q '()))
  '())

(define confusing
  (lambda (ls out)
    (let ((d (var 'd)) (res (var 'res)))
      (conj succeed (conj (pluso res '(1) out) (confusing d res))))))

;;; The 'succeed' before the 'conj' seems to be causing divergence!
(test-check (run/1 #f (q) (confusing q '()))
  (run/1 #f (q) (confusing q '()))
  '())
