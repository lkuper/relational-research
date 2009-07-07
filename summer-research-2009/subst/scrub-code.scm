(load "lib/pmatch.scm")

;; scrub-code: strips statistics-gathering code, extraneous begins,
;; and lhs and rhs out of source code.  Only tested on walk-basic, so
;; far.
(define scrub-code
  (lambda (expr)
    (pmatch expr
      [,atom (guard (not (pair? atom))) atom]
      [((inc-ws-steps) . ,cdr) (scrub-code cdr)]
      [((inc-ws-calls ,x) . ,cdr) (scrub-code cdr)]
      [((inc-ws-recrs) . ,cdr) (scrub-code cdr)]
      [((ws-found-match) . ,cdr) (scrub-code cdr)]
      [(lhs . ((car ,e))) `(caar ,(scrub-code e))]
      [(rhs . ((car ,e))) `(cdar ,(scrub-code e))]
      ;; this one's gross, but I don't have a better way at the moment
      [(begin . ,e) (car (scrub-code e))]
      [,otherwise (cons (scrub-code (car expr))
                        (scrub-code (cdr expr)))])))
