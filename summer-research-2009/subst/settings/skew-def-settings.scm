(module settings
  (name dl-worst-case-assoc build-random-assoc-br choose-size-s choose-var
          choose-walk choose-birth-record choose-assoc-repr choose-copy-term
          choose-walk-return)
  (define name "walk-skew-def")
  (define dl-worst-case-assoc #f)
  (define build-random-assoc-br #f)
  (define-syntax choose-var
    (syntax-rules ()
      [(_ var-1 var-2 var-2-k var-2-kd var-bst) var-2-kd]))
  (define-syntax choose-walk
    (syntax-rules ()
      [(_ wassq wbasic wrhs wstep wsref wsreff wtrie wbst wskew wskewd
          wfb wfb-opt wno-rec-stk wno-rec-stkf wpinch wpinch-s wfoldr) wskewd]))
  (define-syntax choose-size-s
    (syntax-rules ()
      [(_ size-s-l size-s-t size-s-bst size-s-skew size-s-skew-def) size-s-skew-def]))
  (define-syntax choose-birth-record
    (syntax-rules ()
      [(_ nbr cbr sbr) nbr]))
  (define-syntax choose-assoc-repr
    (syntax-rules ()
      [(_ sl dl t b k kd) kd]))
  (define-syntax choose-copy-term
    (syntax-rules ()
      [(_ n k kd) kd]))
  (define-syntax choose-walk-return
    (syntax-rules ()
      [(_ sv mv) sv])))
