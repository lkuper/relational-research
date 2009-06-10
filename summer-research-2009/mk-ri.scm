(load "mk.scm")

(run* (q)
  (exist (x y z)
    (== x 5)
    (conde
      [(== z x) (== `(,z ,x) q)]
      [(== z 6) (== `(,x ,z) q)])))


