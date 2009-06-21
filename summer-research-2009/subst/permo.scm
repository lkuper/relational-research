(module permo 
  (permo)
  (import (scheme) (mk) (mktests)) 

(define permo-aux
  (lambda (iwork slide swork res out)
    ;(exist (prefix prefix^ e e0 e* r r* y y* s s* res^)
    ;(exist (prefix^ s* s res^ y y* r* r e prefix e* e0)
    (exist (prefix^ res^ y y* r* r s* s e prefix e* e0)
      (conde
        [(== '() iwork)
         (== `(,prefix ,e ()) slide)
         (== '() swork)
         (== res out)]
        [(== `(,e0 . ,e*) iwork)
         (== `(,prefix ,e ()) slide)
         (== '() swork)
         (== `(,r . ,r*) res)
         (permo-aux e* `(() ,e0 ,r) r* `((,e0 . ,r)) out)]
        [(== `(,prefix ,e ()) slide)
         (== `(,y . ,y*) swork)
         (permo-aux iwork `(() ,e ,y) y* `((,e . ,y) . ,res) out)]
        [(== `(,prefix ,e (,s . ,s*)) slide)
         (appendo prefix `(,s) prefix^)
         (appendo prefix^ `(,e . ,s*) res^)
         (permo-aux iwork `(,prefix^ ,e ,s*) swork `(,res^ . ,res) out)]))))

(define permo
  (lambda (ls out)
    (exist (a b)
      (conde
        [(== '() ls) (== ls out)]
        [(== `(,a . ,b) ls) (permo-aux ls '(() () ()) '() '(()) out)]))))

)
