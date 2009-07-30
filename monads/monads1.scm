'(load "monads0.scm")
;;; Now for call/cc

(define k-as-proc
  (lambda (k)
    (lambda (a)
      (lambda (_) (k a)))))

(define call/cck
  (lambda (f)
    (lambda (k)
      ((f (k-as-proc k)) k))))

;; Here, _ is the runtime continuation and k is the grabbed
;; continuation.  (lambda (k) (lambda (a) (lambda (_) (k a)))) can be
;; thought of as "packaging" around the grabbed continuation.  Notice
;; that _ doesn't occur in the body of (lambda (_) (k a)), because the
;; runtime continuation "disappears" when we invoke a grabbed continuation
;; (as if there were a law of conservation of continuations!)  Really this
;; is because there is only one active control flow per computation.
;; With continuations, however, there can be dormant control flows, but
;; once we invoke one of them, the other disappears unless it is saved
;; somewhere beforehand.

;; ((f (k-as-proc k)) k) is an "if ... then ... else" mechanism for
;; dealing with the two possible situations of "default" use of k and
;; "explicit" use of k.

;; I need the unit and bind of the continuation monad.

(define unit
  (lambda (v)
    (lambda (k)
      (k v))))

(define bind
  (lambda (comp f)
    (lambda (k)
      (comp (lambda (v) ((f v) k))))))

(define-syntax do*
  (syntax-rules ()
    ((_ ((x0 comp0)) comp-body) (bind comp0 (lambda (x0) comp-body)))
    ((_ ((x0 comp0) (x comp) ...) comp-body)
     (bind comp0 (lambda (x0) (do* ((x comp) ...) comp-body))))))

;;; We know we cannot write (f (g x)), when both f and g are serious.
;;; So, (exit (exit 0)) is similarly illegal.  We need a bind.
;;; So, the __ is bound in the do*, but the (exit __) in the body
;;; of the do* is dropped as one might expect with first-class continuations.
;;; Furthermore, if the expression had been (exit (exit (exit 0))), this
;;; would have required (do* ((__ (exit 0))
;;;                           (__ (exit __))
;;;                       (exit __))), etc.

(define product
  (lambda (ls)
    (call/cck
      (lambda (exit)
        (letrec
          ((prod
             (lambda (ls)
               (cond
                 ((null? ls) (unit 1))
                 ((pair? (car ls))
                  (do* ((a (prod (car ls)))
                        (d (prod (cdr ls))))     
                    (unit (* a d))))
                  ((= (car ls) 0) (do* ((__ (exit 0)))
                                    (exit __)))
                  (else (do* ((d (prod (cdr ls))))
                          (unit (* (car ls) d))))))))
               (prod ls))))))

(write (= 0
          ((product '((((((1 8 3)) 8) 7 0 8 9) 8) 9)) (lambda (x) x))))
(newline)

(write (= 13934592
          ((product '((((((1 8 3)) 8) 7 2 8 9) 8) 9)) (lambda (x) x))))
(newline)

;(load "monads2.scm")
