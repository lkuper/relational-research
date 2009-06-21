(module mkstats 
  (print-ws print-ws-totals clear-ws ws-found-match 
   inc-ws-calls inc-ws-steps inc-ws-recrs
   inc-ws-safe-calls inc-ws-safe-steps inc-ws-safe-recrs)
  (import (scheme))

; stats
(define-record walk-stats (calls steps recrs scalls ssteps srecrs
;(define-struct walk-stats (calls steps recrs scalls ssteps srecrs
                           tcalls tsteps trecrs tscalls tssteps tsrecrs
                           last-len last-steps frac-visited found-first
                           first-steps tot-len))
(define ws (make-walk-stats 0 0 0 0 0 0
                            0 0 0 0 0 0
                            -1 0 0. #f
                            0 0))
(define clear-ws
  (lambda ()
    (set-walk-stats-calls! ws 0)
    (set-walk-stats-steps! ws 0)
    (set-walk-stats-recrs! ws 0)
    (set-walk-stats-scalls! ws 0)
    (set-walk-stats-ssteps! ws 0)
    (set-walk-stats-srecrs! ws 0)
    (set-walk-stats-last-len! ws -1)
    (set-walk-stats-last-steps! ws 0)
    (set-walk-stats-frac-visited! ws 0.)
    (set-walk-stats-found-first! ws #f)
    (set-walk-stats-first-steps! ws 0)
    (set-walk-stats-tot-len! ws 0)))
;(define ws-found-match
  ;(lambda ()
    ;(set-walk-stats-found-first! ws #t)))
;(define inc-ws-calls
  ;(lambda (s)
    ;(if (zero? (walk-stats-last-len ws))
      ;(set-walk-stats-frac-visited! ws (add1 (walk-stats-frac-visited ws)))
      ;(if (> (walk-stats-last-len ws) 0)
        ;(set-walk-stats-frac-visited! ws (+ (exact->inexact
                                              ;(/ (walk-stats-last-steps ws)
                                                 ;(walk-stats-last-len ws)))
                                            ;(walk-stats-frac-visited ws)))))
    ;(set-walk-stats-last-len! ws (length s))
    ;;(set-walk-stats-last-len! ws 1)
    ;(set-walk-stats-tot-len! ws (+ (walk-stats-last-len ws) (walk-stats-tot-len ws)))
    ;(set-walk-stats-last-steps! ws 0)
    ;(set-walk-stats-found-first! ws #f)
    ;(set-walk-stats-calls! ws (add1 (walk-stats-calls ws)))
    ;(set-walk-stats-tcalls! ws (add1 (walk-stats-tcalls ws)))))
;(define inc-ws-steps
  ;(lambda ()
    ;(if (not (walk-stats-found-first ws))
       ;(set-walk-stats-first-steps! ws (add1 (walk-stats-first-steps ws))))
    ;(set-walk-stats-steps! ws (add1 (walk-stats-steps ws)))
    ;(set-walk-stats-last-steps! ws (add1 (walk-stats-last-steps ws)))
    ;(set-walk-stats-tsteps! ws (add1 (walk-stats-tsteps ws)))))
;(define inc-ws-recrs
  ;(lambda ()
    ;(set-walk-stats-recrs! ws (add1 (walk-stats-recrs ws)))
    ;(set-walk-stats-trecrs! ws (add1 (walk-stats-trecrs ws)))))
;(define inc-ws-safe-calls
  ;(lambda ()
    ;(set-walk-stats-scalls! ws (add1 (walk-stats-scalls ws)))
    ;(set-walk-stats-tscalls! ws (add1 (walk-stats-tscalls ws)))))
;(define inc-ws-safe-steps
  ;(lambda ()
    ;(set-walk-stats-ssteps! ws (add1 (walk-stats-ssteps ws)))
    ;(set-walk-stats-tssteps! ws (add1 (walk-stats-tssteps ws)))))
;(define inc-ws-safe-recrs
  ;(lambda ()
    ;(set-walk-stats-srecrs! ws (add1 (walk-stats-srecrs ws)))
    ;(set-walk-stats-tsrecrs! ws (add1 (walk-stats-tsrecrs ws)))))
(define print-ws
  (lambda ()
    (if (zero? (walk-stats-last-len ws))
      (set-walk-stats-frac-visited! ws (add1 (walk-stats-frac-visited ws)))
      (if (> (walk-stats-last-len ws) 0)
        (set-walk-stats-frac-visited! ws (+ (exact->inexact
                                              (/ (walk-stats-last-steps ws)
                                                 (walk-stats-last-len ws)))
                                            (walk-stats-frac-visited ws)))))
    (set-walk-stats-last-len! ws -1)
    (let ([wc (walk-stats-calls ws)]
          [ws (walk-stats-steps ws)]
          [wr (walk-stats-recrs ws)]
          [wsc (walk-stats-scalls ws)]
          [wss (walk-stats-ssteps ws)]
          [wsr (walk-stats-srecrs ws)]
          [tl (walk-stats-tot-len ws)]
          [fv (walk-stats-frac-visited ws)]
          [fs (walk-stats-first-steps ws)])
      (printf "calls:~d steps:~d recursions:~d " wc ws wr)
      (printf "scalls:~d ssteps:~d srecursions:~d\n" wsc wss wsr)
      (printf "avg-steps-per-call:~s\navg-recrs-per-call:~s\n"
              (if (> wc 0) (exact->inexact (/ ws wc)) 0) (if (> wc 0) (exact->inexact (/ wr wc)) 0))
      (printf "avg-len:~s\navg-percent-walked:~s\navg-depth-to-first-match:~s\n"
              (if (> tl 0) (exact->inexact (/ tl wc)) 0)
              (if (> wc 0) (* 100. (exact->inexact (/ fv wc))) 0)
              (if (> wc 0) (exact->inexact (/ fs wc)) 0))
      (printf "avg-ssteps-per-call:~s\navg-srecrs-per-call:~s\n"
              (if (> wsc 0) (exact->inexact (/ wss wsc)) 0) (if (> wsc 0) (exact->inexact (/ wsr wsc)) 0)))))
(define print-ws-totals
  (lambda ()
    (let ([wc (walk-stats-tcalls ws)]
          [ws (walk-stats-tsteps ws)]
          [wr (walk-stats-trecrs ws)]
          [wsc (walk-stats-tscalls ws)]
          [wss (walk-stats-tssteps ws)]
          [wsr (walk-stats-tsrecrs ws)])
      (printf "total calls:~d total steps:~d total recursions:~d " wc ws wr)
      (printf "total scalls:~d total ssteps:~d total srecursions:~d\n" wsc wss wsr)
      (printf "total avg-steps-per-call:~s\ntotal avg-recrs-per-call:~s\n"
              (if (> wc 0) (exact->inexact (/ ws wc)) 0) (if (> wc 0) (exact->inexact (/ wr wc)) 0))
      (printf "total avg-ssteps-per-call:~s\ntotal avg-srecrs-per-call:~s\n"
              (if (> wsc 0) (exact->inexact (/ wss wsc)) 0) (if (> wsc 0) (exact->inexact (/ wsr wsc)) 0)))))

; uncomment these lines to remove stats
(define-syntax ws-found-match (syntax-rules () [(_) (void)]))
(define-syntax inc-ws-calls (syntax-rules () [(_ s) (void)]))
(define-syntax inc-ws-steps (syntax-rules () [(_) (void)]))
(define-syntax inc-ws-recrs (syntax-rules () [(_) (void)]))
(define-syntax inc-ws-safe-calls (syntax-rules () [(_) (void)]))
(define-syntax inc-ws-safe-steps (syntax-rules () [(_) (void)]))
(define-syntax inc-ws-safe-recrs (syntax-rules () [(_) (void)]))
)
