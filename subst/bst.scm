(module bst
  (bst:ext bst:lookup bst:empty bst:size bst:hash)
  (import scheme)

  (define-record bst-node (idx data left right))

  ;; 'DE for 'dead-end'!

  ;; (define bst:empty
  ;; (make-bst-node 0 'DE 'DE
  ;; 'DE))

  (define bst:empty
    (lambda ()
      (make-bst-node 0 'DE 'DE 'DE)))

  (define flatten-bst
    (lambda (t)
      (if (bst-node? t)
          (list (flatten-bst (bst-node-left t)) (bst-node-idx t)
                (flatten-bst (bst-node-right t)))
          '())))

  ;; add value v with key to trie t.
  (define bst:ext
    (lambda (n v t)
      (if (bst-node? t)
          (let ((idx (bst-node-idx t)))
            (cond
              ((equal? n idx) (make-bst-node n v (bst-node-left t)
                                             (bst-node-right t)))
              ((< idx n) (make-bst-node idx
                                        (bst-node-data t)
                                        (bst-node-left t)
                                        (bst:ext n v (bst-node-right t))))

              (else (make-bst-node idx
                                   (bst-node-data t)
                                   (bst:ext n v (bst-node-left t))
                                   (bst-node-right t)))))
          (make-bst-node n v 'DE 'DE))))

  (define bst:lookup
    (lambda (k t)
      (if (bst-node? t)
          (cond
            ((equal? (bst-node-idx t) k) (bst-node-data t))
            ((< k (bst-node-idx t)) (bst:lookup k (bst-node-left t)))
            (else (bst:lookup k (bst-node-right t))))
          'DE)))

  (define bst:size
    (lambda (t)
      (if (bst-node? t)
          (+ (bst:size (bst-node-left t))
             (bst:size (bst-node-right t))
             (if (eq? (bst-node-data t) 'DE) 0 1))
          0)))

  ;; we're assuming that there are no collisions (which is true
  ;; mathematically, but perhaps not with floating point!).
  (define bst:hash cos)

  ;;(define-syntax lookup-assoc
  ;;(syntax-rules ()
  ;;((_ v s) (lookup-bst (bst:hash (vector-ref v 1)) s))))
  )
