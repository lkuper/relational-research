(import (alphatap))

(define-syntax pp-divergence
  (syntax-rules ()
    ((_ n axioms theorem)
     (let ((max-ticks 500000000))
       (printf "Pelletier Problem ~s:\n" n)
       (printf "*** expecting divergence ***\n")
       (printf "*** using engine with ~s ticks fuel ***\n" max-ticks)
       (printf "-----------------------------------")
       ((make-engine (lambda () (do-prove-th axioms theorem)))
	max-ticks
	(lambda (t v)
	  (error title "infinite loop returned ~s after ~s ticks" v (- max-ticks t)))
	(lambda (e^) (void)))
       (printf "*** problem ~s appears to diverge ***\n" n)
       (printf "-----------------------------------\n\n")))))

(define-syntax pp
  (syntax-rules ()
    ((_ n axioms theorem)
     (let ((max-ticks 5000000))
       (printf "Pelletier Problem ~s:\n" n)
       ((make-engine (lambda () (do-prove-th axioms theorem)))
	max-ticks
	(lambda (t v)
          (void))
	(lambda (e^) (printf "OH NOES\n")))
       (printf "\n\n")))))

;; Remove quote to ignore divergent tests.
(define-syntax pp-divergence
  (syntax-rules ()
    ((_ n axioms theorem)
     (begin
       (printf "Pelletier Problem ~s:\n" n)
       (printf "*** IGNORING DIVERGENT PROBLEM ***\n")
       (printf "-----------------------------------\n")
       (printf "-----------------------------------\n\n")))))


(define-syntax loop
  (syntax-rules ()
    ((_ n e) (let mloop ((num n))
               (cond
                 ((zero? num) (void))
                 (else e (mloop (sub1 num))))))))

(define-syntax pp
  (syntax-rules ()
    ((_ n axioms theorem)
     (begin
       ;(printf "Pelletier Problem ~s:\n" n)
;       (printf "-----------------------------------\n")
       ;(time (loop 100 (do-prove-th axioms theorem))))))) -DCB
       (loop 2 (do-prove-th axioms theorem))))))
;; Pelletier Problems

(define test-short
  (lambda ()
    
;; 1 - 5
;; Micah Linnemeier

(pp 1 '() '(<=> (=> p q) (=> (not q) (not p))))
(pp 2 '() '(=>  (not (not p)) p))
(pp 3 '() '(=> (not (=> p q)) (=> q p)))
(pp 4 '() '(<=> (=> (not p) q) (=> (not q) p)))
(pp 5 '() '(=> (=> (or p q) (or p r)) (or p (=> q r))))

;; 6 - 10
;; Adam Hinz

(pp 6 '() `(or p (not p)))
(pp 7 '() `(or p (not (not (not p)))))
(pp 8 '() `(=> (=> (=> p q) p) p))

(pp 9 '() 
    `(=> (and (or p q)
	      (and
               (or (not p) q)
               (or p (not q))))
	 (not (or (not p) (not q)))))

(pp 10
    `((=> q r)
      (=> r (and p q))
      (=> p (or q r)))
    `(<=> p q))

;; 11 - 15
;; Joe Near

(pp 11 '() '(<=> p p))
(pp 12 '() '(<=> (<=> (<=> p q) r) (<=> p (<=> q r))))
(pp 13 '() '(<=> (or p (and q r)) (and (or p q) (or p r))))
(pp 14 '() '(<=> (<=> p q) (and (or q (not p)) (or (not q) p))))
(pp 15 '() '(<=> (=> p q) (or (not p) q)))

;; 16 - 20
;; Micah Linnemeier

(pp 16 '() '(or (=> p q) (=> q p)))

(pp 17 '()
    `(<=> (=> (and p (=> q r)) s)
          (and (or (not p) (or q s)) (or (not p) (or (not r) s)))))

(pp 18 '() `,(E y ,(A x (=> (f ,y) (f ,x)))))

(pp 19 '()
    `,(E x ,(A y ,(A z (=>
                        (=> (p ,y) (q ,z))
                        (=> (p ,x) (q ,x)))))))

(pp 20 '() 
    `,(A x ,(A y ,(E z ,(A w 
                           (=>
                            (=> (and (p ,x) (q ,y))
                                (and (r ,z) (s ,w)))
                            ,(E x ,(E y
                                      (=>
                                       (and (p ,x) (q ,y))
                                       ,(E z
                                           (r ,z)))))))))))

))

(define test
  (lambda ()
    (test-short)
;; 21 - 30
;; Micah Linnemeier

(pp 21
    `(,(E x (=> p (f ,x))) ,(E x (=> (f ,x) p)))
    `,(E x (<=> p (f ,x))))

(pp 22 '() `(=> ,(A x (<=> p (f ,x))) (<=> p ,(A x (f ,x)))))
(pp 23 '() `(<=> ,(A x (or p (f ,x))) (or p ,(A x (f ,x)))))

(pp 24
    `((not ,(E x (and (s ,x) (q ,x))))
      ,(A x (=> (p ,x) (or (q ,x) (r ,x))))
      (not (=> ,(E x (p ,x)) ,(E x (q ,x))))
      ,(A x (=> (or (q ,x) (r ,x)) (s ,x))))
    `,(E x (and (p ,x) (r ,x))))

(pp 25
    `(,(E x (p ,x))
      ,(A x (=> (f ,x) (and (not (g ,x)) (r ,x))))
      ,(A x (=> (p ,x) (and (g ,x) (f ,x))))
      (or ,(A x (=> (p ,x) (r ,x))) ,(E x (and (p ,x) (r ,x)))))
    `,(E x (and (p ,x) (r ,x))))

(pp 26
    `((<=> ,(E x (p ,x)) ,(E x (q ,x)))
      ,(A x ,(A y (=> (and (p ,x) (q ,y)) (<=> (r ,x) (s ,y))))))
    `(<=> ,(A x (=> (p ,x) (r ,x))) ,(A x (=> (q ,x) (s ,x)))))

(pp 27
    `(,(E x (and (f ,x) (not (g ,x))))
      ,(A x (=> (f ,x) (h ,x)))
      ,(A x (=> (and (j ,x) (i ,x)) (f ,x)))
      (=> ,(E x (and (h ,x) (not (g ,x))))
          ,(A x (=> (i ,x) (not (h ,x))))))
    `,(A x (=> (j ,x) (not (i ,x)))))

(pp 28
    `(,(A x (=> (p ,x) ,(A x (q ,x))))
      (=> ,(A x (or (q ,x) (r ,x))) ,(E x (and (q ,x) (s ,x))))
      (=> ,(E x (s ,x)) ,(A x (=> (f ,x) (g ,x)))))
      `,(A x (=> (and (p ,x) (f ,x)) (g ,x))))

(pp 29
    `((and ,(E x (f ,x)) ,(E x (g ,x))))
    `(<=>
      (and
       ,(A x (=> (f ,x) (h ,x)))
       ,(A x (=> (g ,x) (j ,x))))
      ,(A x ,(A y (=> (and (f ,x) (g ,y)) (and (h ,x) (j ,y)))))))

(pp 30
    `(,(A x (=> (or (f ,x) (g ,x)) (not (h ,x))))
      ,(A x (=> (=> (g ,x) (not (i ,x))) (and (f ,x) (h ,x)))))
    `,(A x (i ,x)))

    
;; 31 - 40
;; Adam Hinz

(pp 31
    `((not ,(E x (and (f ,x) (or (g ,x) (h ,x)))))
      ,(E x (and (i ,x) (f ,x)))
      ,(A x (=> (not (h ,x)) (j ,x))))
    `,(E x (and (i ,x) (j ,x))))

(pp 32
    `(,(A x (=> (and (f ,x) (or (g ,x) (h ,x))) (i ,x)))
      ,(A x (=> (and (i ,x) (h ,x)) (j ,x)))
      ,(A x (=> (k ,x) (h ,x))))
    `,(A x (=> (and (f ,x) (k ,x)) (j ,x))))

(pp 33
    '()
    `(<=> ,(A x (=> (and (p a) (=> (p ,x) (p b))) (p c)))
          ,(A x (and (or (not (p a)) (or (p ,x) (p c)))
                     (or (not (p a)) (or (not (p b)) (p c)))))))

(pp 34
    '()
    `(<=>
      (<=> ,(E x ,(A y (<=> (p ,x) (p ,y))))
           (<=> ,(E x (q ,x)) ,(A y (q ,y))))
      (<=> ,(E x ,(A y (<=> (q ,x) (q ,y))))
           (<=> ,(E x (p ,x)) ,(A y (p ,y))))))

(pp 35
    '()
    `,(E x ,(E y (=> (p ,x ,y) ,(A x ,(A y (p ,x ,y)))))))

(pp 36
    `(,(A x ,(E y (f ,x ,y)))
      ,(A x ,(E y (g ,x ,y)))
      ,(A x ,(A y (=> (or (f ,x ,y) (g ,x ,y))
                      ,(A z (=> (or (f ,y ,z) (g ,y ,z)) (h ,x ,z)))))))
    `,(A x ,(E y (h ,x ,y))))


(pp 37
    `(,(A z ,(E w ,(A x ,(E y (and (=> (p ,x ,z) (p ,y ,w))
                                   (and (p ,y ,z)
                                        (=> (p ,y ,w) ,(E u (q ,u ,w)))))))))
      ,(A x ,(A z (=> (not (p ,x ,z)) ,(E y (q ,y ,z)))))
      (=> ,(E x ,(E y (q ,x ,y))) ,(A x (r ,x ,x))))
    `,(A x ,(E y (r ,x ,y))))

(pp 38
    '()
    `(<=> ,(A x (=> (and (p a) (=> (p ,x) ,(E y (and (p ,y) (r ,x ,y)))))
                    ,(E z ,(E w (and (p ,z) (and (r ,x ,w) (r ,w ,z)))))))
          ,(A x (and
                 (or (not (p a)) (or (p ,x) ,(E z ,(E w (and (p ,z)
                                                             (and (r ,x ,w)
                                                                  (r ,w ,z)))))))
                 (or (not (p a))
                     (or (not ,(E y (and (p ,y) (r ,x ,y))))
                         ,(E z ,(E w (and (p ,z)
                                          (and (r ,x ,w)
                                               (r ,w ,z)))))))))))

(pp 39
    '()
    `(not ,(E x ,(A y (<=> (f ,y ,x) (not (f ,y ,y)))))))

(pp 40
    '()
    `(=> ,(E y ,(A x (<=> (f ,x ,y) (f ,x ,x))))
         (not ,(A x ,(E y ,(A z (<=> (f ,z ,y) (not (f ,z ,x)))))))))



;; 41 - 50
;; (Assigned to Joe Near)

(pp 41
    `(,(A z ,(E y ,(A x (<=> (F ,x ,y) (and (F ,x ,z) (not (F ,x ,x))))))))
    `(not ,(E z ,(A x (F ,x ,z)))))

(pp 42
    '()
    `(not ,(E y ,(A x (<=> (F ,x ,y) (not ,(E z (and (F ,x ,z) (F ,z ,x)))))))))

(pp 43
    `(,(A x ,(A y (<=> (Q ,x ,y) ,(A z (<=> (F ,z ,x) (F ,z ,y)))))))
    `,(A x ,(A y (<=> (Q ,x ,y) (Q ,y ,x)))))

(pp 44
    `(,(A x (and (=> (F ,x) ,(E y (and (G ,y) (H ,x ,y))))
                 ,(E y (and (G ,y) (not (H ,x ,y))))))
      ,(E x (and (J ,x) ,(A y (=> (G ,y) (H ,x ,y))))))
    `,(E x (and (J ,x) (not (F ,x)))))

(pp 45
    `(,(A x (and (F ,x) ,(A y (=> (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))
                                  ,(A y (and (G ,y) (=> (H ,x ,y) (K ,y))))))))
      (not ,(E y (and (L ,y) (K ,y))))
      ,(E x (and (and (F ,x) ,(A y (=> (H ,x ,y) (L ,y))))
                 ,(A y (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))))))
    `,(E x (and (F ,x) (not ,(E y (and (G ,y) (H ,x ,y)))))))

(pp 46
    `(,(A x (=> (and (F ,x) ,(A y (=> (and (F ,y) (H ,y ,x))
                                      (G ,y))))
                (G ,x)))
      (=> ,(E x (and (F ,x) (not (G ,x))))
          ,(E x (and (F ,x) (and (not (G ,x))
                                 ,(A y (=> (and (F ,y) (not (G ,y))) (J ,x ,y)))))))
      ,(A x ,(A y (=> (and (F ,x) (and (F ,y) (H ,x ,y))) (not (J ,y ,x))))))
    `,(A x (=> (F ,x) (G ,x))))


;(printf "all done!\n")

))

#!eof
;; the STEAMROLLER
(pp 47
    `((and ,(A x (=> (P1 ,x) (P0 ,x))) ,(E x (P1 ,x)))
      (and ,(A x (=> (P2 ,x) (P0 ,x))) ,(E x (P2 ,x)))
      (and ,(A x (=> (P3 ,x) (P0 ,x))) ,(E x (P3 ,x)))
      (and ,(A x (=> (P4 ,x) (P0 ,x))) ,(E x (P4 ,x)))
      (and ,(A x (=> (P5 ,x) (P0 ,x))) ,(E x (P5 ,x)))
      (and ,(E x (Q1 ,x)) ,(A x (=> (Q1 ,x) (Q0 ,x))))
      ,(A x (=> (P0 ,x)
	        (or ,(A y (=> (Q0 ,y) (R ,x ,y)))
                    ,(A y (=> (and
				(P0 ,y)
				(S ,y ,x)
                                ,(E z (and (Q0 ,z) (R ,y ,z))))
                              (R ,x ,y))))))
      ,(A x ,(A y (=> (and (P3 ,y) (or (P5 ,x) (P4 ,x))) (S ,x ,y))))
      ,(A x ,(A y (=> (and (P3 ,x) (P2 ,y)) (S ,x ,y))))
      ,(A x ,(A y (=> (and (P2 ,x) (P1 ,y)) (S ,x ,y))))
      ,(A x ,(A y (=> (and (P1 ,x) (or (P2 ,y) (Q1 ,y))) (not (R ,x ,y)))))
      ,(A x ,(A y (=> (and (P3 ,x) (P4 ,y)) (R ,x ,y))))
      ,(A x ,(A y (=> (and (P3 ,x) (P5 ,y)) (not (R ,x ,y)))))
      ,(A x (=> (or (P4 ,x) (P5 ,x)) ,(E y (and (Q0 ,y) (R ,x ,y))))))
    `,(E x
	,(E y
	   (and
	     (P0 ,x)
	     (P0 ,y)
	     ,(E z (and (Q1 ,z) (R ,y ,z) (R ,x ,y)))))))

'(pp 47
     `((and ,(A x (=> (P1 ,x) (P0 ,x))) ,(E x (P1 ,x)))
       (and ,(A x (=> (P2 ,x) (P0 ,x))) ,(E x (P2 ,x)))
       (and ,(A x (=> (P3 ,x) (P0 ,x))) ,(E x (P3 ,x)))
       (and ,(A x (=> (P4 ,x) (P0 ,x))) ,(E x (P4 ,x)))
       (and ,(A x (=> (P5 ,x) (P0 ,x))) ,(E x (P5 ,x)))
       (and ,(E x (Q1 ,x)) ,(A x (=> (Q1 ,x) (Q0 ,x))))
       ,(A x (=> (P0 ,x)
                 (or ,(A y (=> (Q0 ,y) (R ,x ,y)))
                     ,(A y (=> (and
				(P0 ,y)
				(and (S ,y ,x)
                                     ,(E z (and (Q0 ,z) (R ,y ,z)))))
                               (R ,x ,y))))))
       ,(A x ,(A y (=> (and (P3 ,y) (or (P5 ,x) (P4 ,x))) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P2 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P2 ,x) (P1 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P1 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P1 ,x) (or (P2 ,y) (Q1 ,y))) (not (R ,x ,y)))))
       ,(A x ,(A y (=> (and (P3 ,x) (P4 ,y)) (R ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P5 ,y)) (not (R ,x ,y)))))
       ,(A x (=> (or (P4 ,x) (P5 ,x)) ,(E y (and (Q0 ,y) (R ,x ,y))))))
     `,(E x
          ,(E y
              (and
               (P0 ,x)
               (and (P0 ,y)
                    ,(E z (and (Q1 ,z) (and (R ,y ,z) (R ,x ,y)))))))))

(pp 47
     `(,(A x (=> (P1 ,x) (P0 ,x)))
       ,(E x (P1 ,x))
       ,(A x (=> (P2 ,x) (P0 ,x)))
       ,(E x (P2 ,x))
       ,(A x (=> (P3 ,x) (P0 ,x)))
       ,(E x (P3 ,x))
       ,(A x (=> (P4 ,x) (P0 ,x)))
       ,(E x (P4 ,x))
       ,(A x (=> (P5 ,x) (P0 ,x)))
       ,(E x (P5 ,x))
       ,(E x (Q1 ,x))
       ,(A x (=> (Q1 ,x) (Q0 ,x)))
       ,(A x (=> (P0 ,x)
                 (or ,(A y (=> (Q0 ,y) (R ,x ,y)))
                     ,(A y (=> (and
				(P0 ,y)
				(and (S ,y ,x)
                                     ,(E z (and (Q0 ,z) (R ,y ,z)))))
                               (R ,x ,y))))))
       ,(A x ,(A y (=> (and (P3 ,y) (or (P5 ,x) (P4 ,x))) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P2 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P2 ,x) (P1 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P1 ,y)) (S ,x ,y))))
       ,(A x ,(A y (=> (and (P1 ,x) (or (P2 ,y) (Q1 ,y))) (not (R ,x ,y)))))
       ,(A x ,(A y (=> (and (P3 ,x) (P4 ,y)) (R ,x ,y))))
       ,(A x ,(A y (=> (and (P3 ,x) (P5 ,y)) (not (R ,x ,y)))))
       ,(A x (=> (or (P4 ,x) (P5 ,x)) ,(E y (and (Q0 ,y) (R ,x ,y))))))
     `,(E x
          ,(E y
              (and
               (P0 ,x)
               (and (P0 ,y)
                    ,(E z (and (Q1 ,z) (and (R ,y ,z) (R ,x ,y)))))))))

(pp 48
    `((or (= a b) (= c d))
      (or (= a c) (= b d)))
    `(or (= a d) (= b c)))

(pp 49
    `(,(E x ,(E y ,(A z (or (= ,z ,x) (= ,z ,y)))))
      (and (P a) (P b))
      (not (= a b)))
    `,(A x (P ,x)))

(pp 50
    `()
    `(=> ,(A x (or (F a ,x) ,(A y (F ,x ,y)))) ,(E x ,(A y (F ,x ,y)))))


;; 51 - 55
;; (Assigned to Adam Hinz)
;; all of these diverged.

(pp 51
    `(,(E z ,(E w ,(A x ,(A y (<=> (f ,x ,y) (and (= ,x ,z) (= ,y ,w))))))))
    `,(E z ,(A x (<=> ,(E w ,(A y (<=> (f ,x ,y) (= ,y ,w)))) (= ,x ,z)))))

(pp 52
    `(,(E z ,(E w ,(A x ,(A y (<=> (f ,x ,y) (and (= ,x ,z) (= ,y ,w))))))))
    `,(E w ,(A y (<=> ,(E z ,(A x (<=> (f ,x ,y) (= ,x ,z)))) (= ,y ,w)))))

(pp 53
    `(,(E x ,(E y (and (not (= ,x ,y)) ,(A z (or (= ,z ,x) (= ,z ,y)))))))
    `(<=> ,(E z ,(A x (<=> ,(E w ,(A y (<=> (f ,x ,y) (= ,y ,w))))
                           (= ,x ,z))))
          ,(E w ,(A y (<=> ,(E z ,(A x (<=> (f ,x ,y) (= ,x ,z))))
                           (= ,y ,w))))))

(pp 54
    `(,(A y ,(E z ,(A x (<=> (f ,x ,z) (= ,x ,y))))))
    `(not ,(E w ,(A x (<=> (f ,x ,w)
                           ,(A u (=> (f ,x ,u)
                                     ,(E y (and (f ,y ,u)
                                                (not ,(E z (and (f ,x ,u)
                                                                (f ,z ,y)))))))))))))

(pp 55
    `(,(E x (and (l ,x) (k ,x a)))
      (and (l a) (l b) (l c))
      ,(A x (=> (l ,x) (or (= ,x a) (= ,x b) (= ,x c))))
      ,(A y ,(A x (=> (k ,x ,y) (h ,x ,y))))
      ,(A x ,(A y (=> (k ,x ,y) (not (r ,x ,y)))))
      ,(A x (=> (h a ,x) (not (h c ,x))))
      ,(A x (=> (not (= ,x b)) (h a ,x)))
      ,(A x (=> (not (r ,x a)) (h b ,x)))
      ,(A x (=> (h a ,x) (h b ,x)))
      ,(A x ,(E y (not (h ,x ,y))))
      (not (= a b)))
    `(k a a))

;; 56 - 60 
;; Micah Linnemeier

;In these problems I use fp to mean f the predicate,
;and ff to mean f the function.
;If you are using the original version of 'prove'
;you will have to add these symbols (as well as = ) to the error-checking
;part of 'close-branch'

(pp 56
    '()
    `(<=> ,(A x (=> ,(E y (and (fp ,y) (= ,x (ff ,y))))
                    (fp ,x)))
          ,(A x (=> (fp ,x) (fp (ff ,x))))))

(pp 57
    `((fp (ff a b) (ff b c))
      (fp (ff b c) (ff a c))
      ,(A x ,(A y ,(A z (=> (and (fp ,x ,y) (fp ,y ,z)) (fp ,x ,z))))))
    `(fp (ff a b) (ff a c)))


(pp 58
    `(,(A x ,(A y (= (ff ,x) (gf ,y)))))
    `,(A x ,(A y (= (ff (ff ,x)) (ff (gf ,y))))))

(pp 59
    `(,(A x (<=> (fp ,x) (not (fp (ff ,x))))))
    `,(E x (and (fp ,x) (not (fp (ff ,x))))))

(pp 60
    '()
    `,(A x (<=>
            (fp ,x (ff ,x))
            ,(E y (and
                   ,(A z (=> (fp ,z ,y) (fp ,z (ff ,x))))
                   (fp ,x ,y))))))

;; 61 - 70
;; (Evens Assigned to Adam Hinz)
;; (Odds Assigned to Micah Linnemeier)

;diverges
(pp 61
 `(,(A x ,(A y ,(A z 
		   (= 
		    (ff ,x (ff ,y ,z)) 
		    (ff (ff ,x ,y) , z))))))
 `,(A x ,(A y ,(A z ,(A w 
			 (= 
			  (ff ,x (ff ,y (ff ,z ,w))) 
			  (ff (ff (ff ,x ,y) ,z) ,w)))))))

(pp 62
    `()
    `(=> ,(A x (=> (and (f a)
                        (=> (f ,x) (f (ff ,x))))
                   (f (ff (ff ,x)))))
         ,(A x (and (or (or (not (f a)) (f ,x)) (f (ff (ff ,x))))
                    (or (or (not (f a)) (not (f (ff ,x)))) (f (ff (ff ,x))))))))


;a
;,(A x ,(A y ,(A z (= (ff (ff ,x ,y) ,z) (f ,x (ff ,y ,z))))))
;b
;,(A x (= (ff a ,x) x))
;c
;,(A x ,(E y (= (ff ,y ,x) a)))


;axioms are a, b, and c
;diverges
(pp 63
    `(,(A x ,(A y ,(A z (= (ff (ff ,x ,y) ,z) (f ,x (ff ,y ,z))))))
      ,(A x (= (ff a ,x) ,x))
      ,(A x ,(E y (= (ff ,y ,x) a))))
    `,(A x ,(A y ,(A z (=> (= (ff ,x ,y) (ff ,z ,y)) (= ,x ,z))))))

;axioms are a,b, and c
(pp 64
    `(,(A x ,(A y ,(A z (= (ff (ff ,x ,y) ,z) (f ,x (ff ,y ,z))))))
      ,(A x (= (ff a ,x) ,x))
      ,(A x ,(E y (= (ff ,y ,x) a))))
    `,(A x ,(A y (=> (= (f ,y ,x) a) (= (f ,x ,y) a)))))

;axioms are a and b
(pp 65
    `(,(A x ,(A y ,(A z (= (ff (ff ,x ,y) ,z) (ff ,x (ff ,y ,z))))))
      ,(A x (= (ff a ,x) ,x)))
    `(=> 
       ,(A x (= (ff ,x ,x) a)) 
       ,(A x ,(A y (= (ff ,x ,y) (ff ,y ,x))))))


;here t is a predicate and i is a function (I think)

;a
;,(A x ,(A y (t (i ,x (i ,y ,x)))))
;b
;,(A x ,(A y (t (i (i ,x (i ,y ,z) ) (i (i ,x ,y) (i ,x ,z))))))
;c
;,(A x ,(A y (t (i (i (n x) (n y)) (i (,y ,x))))))
;d
;,(A x ,(A y (=> (and (t (i ,x ,y)) (t ,x)) (t ,y))))

;axioms are a, b, c, and d
(pp 66
    `(,(A x ,(A y (t (i ,x (i ,y ,x)))))
      ,(A x ,(A y ,(A z (t (i (i ,x (i ,y ,z) ) (i (i ,x ,y) (i ,x ,z)))))))
      ,(A x ,(A y (t (i (i (n ,x) (n ,y)) (i ,y ,x)))))
      ,(A x ,(A y (=> (and (t (i ,x ,y)) (t ,x)) (t ,y)))))
    `,(A x (t (i ,x (n (n ,x))))))
    

;axioms are a, b, c, and d
;diverges
(pp 67
    `(,(A x ,(A y (t (i ,x (i ,y ,x)))))
      ,(A x ,(A y ,(A z (t (i (i ,x (i ,y ,z) ) (i (i ,x ,y) (i ,x ,z)))))))
      ,(A x ,(A y (t (i (i (n ,x) (n ,y)) (i ,y ,x)))))
      ,(A x ,(A y (=> (and (t (i ,x ,y)) (t ,x)) (t ,y)))))
    `,(A x (t (i (n (n ,x)) ,x))))

;uses axioms a,b, and d, and replaces c with the following:
; ,(A x ,(A y (t (i (i ,y ,x) (i (n x) (n y))))))

(pp 68
    `(,(A x ,(A y (t (i ,x (i ,y ,x)))))
      ,(A x ,(A y ,(A z (t (i (i ,x (i ,y ,z) ) (i (i ,x ,y) (i ,x ,z)))))))
      ,(A x ,(A y (t (i (i ,y ,x) (i (n ,x) (n ,y))))))
      ,(A x ,(A y (=> (and (t (i ,x ,y)) (t ,x)) (t ,y)))))
    `,(A x (t (i ,x (n (n ,x))))))

;; 71-75
;; (Not Yet Assigned)
