; expect: 1
; A one-constructor match binds outward (DESIGN.md section 16): in run position it runs and binds the
; field Const, and inside a body it is a one-branch match wrapping the rest.

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))

(def-lvl X)
(def-fns X $ (many peek : (many (Box) b) -> (many (Nat) n))
  (let-match many b (MkBox v))
  v)

(let ((many b)) (MkBox (Succ (Zero))))
(let-match many b (MkBox w))
(peek (MkBox w))
