; error: return does not satisfy `at`
; Two `is`-equal blocks: boxing one says nothing about the slot of the other, however their contents compare.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (many (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many f : (many (MyNat) p) (many (MyNat) q) (erased (Eq (MyNat) p q) e) -> (many (MyNat) r at p))
  (let-match erased e (Refl _ _))
  (let ((many b)) (place-at-many _ q))
  (let-match erased (placed-slot _ _ _ b) (Refl _ _))
  (unplace-at-many _ _ _ b))
