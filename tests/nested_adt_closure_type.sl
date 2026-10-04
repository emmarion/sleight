; expect: 2
; A def-adts inside a body whose field is typed by the enclosing function's type parameter A, closed over.

(def-lvl X)
(def-fns X $ (many wrap : (erased Type A) (many A x) -> (many A y))
  (def-adts $ (Box : -> Type)
    enum
    (many MkBox : (many A v) -> (Box)))
  (let ((many b)) (MkBox x))
  (match many b ((A r))
    ((MkBox v) v)))
(wrap (Nat) (Succ (Succ (Zero))))
