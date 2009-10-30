; FIXME: right now, must use full path because this gets loaded by a file in
                                        ;        another directory. Is there a better way?
(load "~/repos/iucs-relational-research/subst/lib/pmatch.scm")

(define functions '((walk-basic . walk)
                    (unify-sv . unify)
                    (step . step-sref)
                    (walk-no-rec-stkf . walk-flatten)
                    (walk-no-rec-stkf-back . walk-flatten-back)
                    (walk-fb . walk-front-back)
                    (walk-no-rec-stk . walk-reverse-list)
                    (walk-no-rec-stk-back . walk-reverse-list-back)
                    (walk-pinch-s . walk-pinch)
                    (pinch-s . pinch)
                    (pinch-s-find . pinch-find)
                    (ret-no-rec-stkf . ret-flatten)))

;; scrub-code: strips statistics-gathering code, extraneous begins,
;; and the like out of source code.
(define scrub-code
  (lambda (expr)
    (pmatch expr
      [,atom (guard (not (pair? atom))) atom]
      ;; remove stats
      [((inc-ws-steps) . ,cdr) (scrub-code cdr)]
      [((inc-ws-calls ,x) . ,cdr) (scrub-code cdr)]
      [((inc-ws-recrs) . ,cdr) (scrub-code cdr)]
      [((ws-found-match) . ,cdr) (scrub-code cdr)]

      ;; Don't show code for lhs, rhs, or var-birth
      [(define-syntax lhs ,d) 'ignore]
      [(define-syntax rhs ,d) 'ignore]
      [(define var-birth ,d) 'ignore]

      ;; function definition rename rules
      [(define . ,d)
       (cond
         ((assq (car d) functions) => (lambda (p)
                                        `(define ,(cdr p) . ,(scrub-code (cdr d)))))
         (else `(define . ,(scrub-code d))))]

      ;; this one's gross, but I don't have a better way at the moment
      ;; function application rename rules
      [(,f . ,d) (guard (assq f functions))
       `(,(cdr (assq f functions)) . ,(scrub-code d))]
      [(begin . ,e) (car (scrub-code e))]
      [,otherwise (cons (scrub-code (car expr))
                        (scrub-code (cdr expr)))])))

(let* ([input-file (cadr (command-line))]
       [p (open-input-file input-file)])
  (let loop ((code (read p)))
    (cond
      ((eof-object? code) (void))
      (else (begin
              (let ([scrubbed (scrub-code code)])
                (if (not (equal? scrubbed 'ignore))
                    (begin
                      (pretty-print (scrub-code code))
                      (newline)))
                (loop (read p))))))))
