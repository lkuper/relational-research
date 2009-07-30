;; Thanks to Steve Ganz

;; Here is the original rember*8

(define rember*8
  (lambda (l)
    (cond
      ((null? l) '())
      ((pair? (car l)) (cons (rember*8 (car l)) (rember*8 (cdr l))))
      ((and (number? (car l)) (= (car l) 8)) (rember*8 (cdr l)))
      (else (cons (car l) (rember*8 (cdr l)))))))

(define test
  (lambda ()
    (pretty-print (rember*8 '(2 3 (8 4 8) 8 () 2)))))

(test)

;; Here are four ways to look at things:
;; First, we use unit and star with an extra operator: incr-num!.

(define unit
  (lambda (x)
    (lambda (s)
      `(,x . ,s))))

(define star ;;; choose one of star or bind.
  (lambda (recvr)
    (lambda (comp)
      (lambda (s)
        (let ((pr (comp s)))
          ((recvr (car pr)) (cdr pr)))))))

(define bind ;;; choose one of star or bind.
  (lambda (comp recvr)
    (lambda (s)
      (let ((pr (comp s)))
        ((recvr (car pr)) (cdr pr))))))

(define incr-num!
  (lambda ()
    (lambda (s)
      `(__ . ,(add1 s)))))

(define rember*8
  (lambda (l)
    (cond
      ((null? l) (unit '()))
      ((pair? (car l))
       ((star
          (lambda (a)
            ((star (lambda (d) (unit (cons a d))))
             (rember*8 (cdr l)))))
        (rember*8 (car l))))
      ((and (number? (car l)) (= (car l) 8)
       ((star (lambda (__) (rember*8 (cdr l))))
        (incr-num!))))
      (else
       ((star (lambda (d) (unit (cons (car l) d))))
        (rember*8 (cdr l)))))))

(define run
  (lambda (comp)
    (comp 0)))

(define test
  (lambda ()
    (pretty-print (run (rember*8 '(2 3 (8 4 8) 8 () 2))))))

(test)
;; ((2 3 (4) () 2) . 3)

;; The last 3 is the number of eights removed.

;; In the second way, we have replaced star by bind, which looks
;; very cps-ish, but we have lost the "k" in the recvr.

(define rember*8
  (lambda (l)
    (cond
      ((null? l) (unit '()))
      ((pair? (car l))
       (bind (rember*8 (car l))
         (lambda (a)
           (bind (rember*8 (cdr l))
             (lambda (d)
               (unit (cons a d)))))))
      ((and (number? (car l)) (= (car l) 8))
       (bind (incr-num!)
         (lambda (__)
           (rember*8 (cdr l)))))
      (else
       (bind (rember*8 (cdr l))
         (lambda (d)
           (unit (cons (car l) d))))))))

(test)
;;;;;

;; In the third way, we have a macro do* that is built from bind.

(define-syntax do*
  (syntax-rules ()
    ((_ ((x0 comp0)) comp-body) (bind comp0 (lambda (x0) comp-body)))
    ((_ ((x0 comp0) (x comp) ...) comp-body)
     (bind comp0 (lambda (x0) (do* ((x comp) ...) comp-body))))))

(define rember*8
  (lambda (l)
    (cond
      ((null? l) (unit '()))
      ((pair? (car l))
       (do* ((a (rember*8 (car l)))
             (d (rember*8 (cdr l))))
         (unit (cons a d))))
      ((and (number? (car l)) (= (car l) 8))
       (do* ((__ (incr-num!)))
         (rember*8 (cdr l))))
      (else
       (do* ((d (rember*8 (cdr l))))
         (unit (cons (car l) d)))))))

(test)
;;;;;

;; In the fourth way, we have a macro do* that is built from star.

(define-syntax do*
  (syntax-rules ()
    ((_ ((x0 comp0)) comp-body)
     ((star (lambda (x0) comp-body)) comp0))
    ((_ ((x0 comp0) (x comp) ...) comp-body)
     ((star (lambda (x0) (do* ((x comp) ...) comp-body))) comp0))))

;;; Same rember*8, but do* has to be re-expanded.

(define rember*8  
  (lambda (l)
    (cond
      ((null? l) (unit '()))
      ((pair? (car l))
       (do* ((a (rember*8 (car l)))
             (d (rember*8 (cdr l))))
         (unit (cons a d))))
      ((and (number? (car l)) (= (car l) 8))
       (do* ((__ (incr-num!)))
         (rember*8 (cdr l))))
      (else
       (do* ((d (rember*8 (cdr l))))
         (unit (cons (car l) d)))))))

(test)
