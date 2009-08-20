(module walktests 
  (run-all-walktests)
  (import (scheme) (mk) (mktests) (mkstats) (permo) (settings) (zebra))

  (define run-all-walktests
    (lambda ()
      (define long-tests #f)
      (printf "WALK ~a\n" name)

      ; tests

      (printf "TEST mktests\n")
      (clear-ws)
      (time (if long-tests (run-all-mktests) (run-all-mktests-short)))
      (print-ws)

      (printf "TEST logo\n")
      (clear-ws)
      (time (if long-tests (run-logo 9) (run-logo 1)))
      (print-ws)

      (printf "TEST wc-assoc\n")
      (clear-ws)
      (let [(n (if long-tests 30000 300))]
        (let [(r (build-wc-s n))]
          (time
            (walk (car r) (cdr r)))))
            ;(test-check "worst-case hand-build-assoc"
              ;(walk (car r) (cdr r)) ; some versions of walk return multiple values.. gr.
              ;1))))
      (print-ws)

      (printf "TEST wc-assoc-mk\n")
      (clear-ws)
      (if long-tests
        (time (load "biggerwalk.scm"))
        (time (load "bigwalk.scm")))
      (print-ws)

      (printf "TEST permo\n")
      (clear-ws)
      (let [(n (if long-tests 8 9))]
        (time
          (let loop ((i 1))
            (cond
              [(zero? i) '()]
              [else (begin
                      (run n (q)
                        (exist (r s)
                          (permo r s)
                          (== `(,r ,s) q)))
                      (loop (sub1 i)))]))))
      (print-ws)

      (printf "TEST rand-assoc\n")
      (clear-ws)
      (if long-tests
        (random-assoc-test 4000 4000 1000 150000 build-random-assoc-br (equal? name "walk-skew"))
        (random-assoc-test 10 10 5 10000 build-random-assoc-br (equal? name "walk-skew")))
      (print-ws)

      (printf "TEST appendo\n")
      (clear-ws)
      (let [(n (if long-tests 1200 50))]
        (time
          (run n (x)
            (exist (y z)
              (appendo x y z)))))
      (print-ws)

      (printf "TEST leantap\n")
      (clear-ws)
      (load "leantap-test.scm")
      (time (if long-tests (test) (test-short)))
      (print-ws)

      (printf "TEST zebra\n")
      (clear-ws)
      (time (test-zebra (if long-tests 1000 20)))
      (pretty-print (zebrao))
      (print-ws)

      ;(time (run 1 (q) (test-unification-order-1 100000)))
      ;(time (run 1 (q) (test-unification-order-2 1000 q)))

      (print-ws-totals)
      ))

  (define test-unification-order-1
    (lambda (n)
      (cond
        [(zero? n) succeed]
        [else (exist (z y x w) ; reverse order on petite, so w,x,y,z
                (== w 1) (== x 2) (== y 3) (== z 4) ; fast
                ;(== z 1) (== y 2) (== x 3) (== w 4) ; slow
                (test-unification-order-1 (sub1 n)))])))

  (define test-unification-order-2
    (lambda (n q)
      (cond
        [(zero? n) succeed]
        [else (exist (z y x w) ; reverse order on petite, so w,x,y,z
                (== w q) (== x 2) (== y 3) (== z 4) ; fast
                ;(== q w) (== x 2) (== y 3) (== z 4) ; slow
                (test-unification-order-2 (sub1 n) q))])))

  ;;;---------------------------------------------------------------------------
  ;;; functions for building worst-case associations 
  ;;;---------------------------------------------------------------------------

  (define build-wc-s-aux
    (lambda (n v-prev s)
      (cond
        [(zero? n) (cons 'dummy s)]
        [else (let* ([v^ (var n s)]
                     [r* (build-wc-s-aux (sub1 n) v^ s)]
                     [v-last (if (= n 1) v^ (car r*))])
                (cons v-last (ext-s-init v^ v-prev (cdr r*))))])))

  (define build-wc-s
    (lambda (n)
      (let* ([s (empty-s)]
             [v1 (var (add1 n) s)]
             [r* (build-wc-s-aux n v1 s)])
        (cons (car r*) (ext-s-init v1 1 (cdr r*))))))

  ;;;---------------------------------------------------------------------------
  ;;; functions for building random associations
  ;;;---------------------------------------------------------------------------

  (define any
    (lambda (ls)
      (car (list-tail ls (random (length ls))))))

  (define build-vars
    (lambda (n s)
      (cond
        [(zero? n) '()]
        [(cons (var n s) (build-vars (sub1 n) s))])))

  (define build-vals
    (lambda (n)
      (cond
        [(zero? n) '()]
        [(cons n (build-vals (sub1 n)))])))

  (define build-random-assoc
    (lambda (s varl vall n born do_birth_recs)
      (let loop ([s s] [n n] [born born])
        (cond
          [(zero? n) (values s born)]
          [else (let* ([x (any varl)]
                       [v (any (append born vall))]
                       [born^ (if (memq x born) born (cons x born))]
                       [origx (var-value x)]
                       [s^ (unify-safe x v s)])
                  (cond
                    [s^ (begin
                          (if (and do_birth_recs (not (eq? born^ born)))
                            (vector-set! x 0 s))
                          (loop s^ (sub1 n) born^))]
                    [else (loop s n born)]))]))))

  (define random-walks-sv
    (lambda (n varl s)
      (cond
        [(zero? n) '()]
        [else (cons (walk (any varl) s) (random-walks-sv (sub1 n) varl s))])))
  (define random-walks-mv
    (lambda (n varl s)
      (cond
        [(zero? n) '()]
        [else (let-values ([(v s^) (walk (any varl) s)])
                (cons v (random-walks-mv (sub1 n) varl s)))])))

  (define opt-ext-s-init
    (lambda (v s)
      (cond
        [(null? v) s]
        [else (ext-s-init (car v) (car v) (opt-ext-s-init (cdr v) s))])))
  (define random-assoc-test
    (lambda (nvars nvals n m do_birth_recs do_ext_s_init)
      (let* ([s (empty-s)]
             [varl (build-vars nvars s)]
             [vall (build-vals nvals)])
        (let-values ([(s valid-vars)
                      (build-random-assoc (if do_ext_s_init
                                            (opt-ext-s-init varl s) s)
                                          varl vall n '() do_birth_recs)])
        (time (random-walks m valid-vars s))))))

; random walks
(define-syntax random-walks
  (syntax-rules ()
    [(_ n v s) ((choose-walk-return random-walks-sv random-walks-mv) n v s)]))
)
