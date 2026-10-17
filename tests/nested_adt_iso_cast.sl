; expect: 0
; Equating two def-adts types that capture different parameters equates the parameters: in the Refl
; branch, x of type A is returned at C.

(def-lvl X)
(def-fns X $ (many outer : (erased Type A) (erased Type C) (many A a) -> (many (Nat) n))
  (def-adts $ (Bx : -> Type) enum (many K1 : (many A v) -> (Bx)))
  (def-adts $ (By : -> Type) enum (many K2 : (many C v) -> (By)))
  (def-fns X $ (many cast : (erased (Eq Type (Bx) (By)) p) (many A x) -> (many C y))
    (match erased p ((C r))
      ((Refl _ _) x)))
  (Zero))
(outer (Nat) (Nat) (Zero))
