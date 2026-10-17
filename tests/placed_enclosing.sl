; expect: (MySucc $ MySucc $ MyZero)
; A constructor's field placed at the slot of a variable of the enclosing scope: the destructure's `placed-slot`
; puts the field back where that variable is.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many wrap-unwrap : (unique (MyNat) n0) -> (unique (MyNat) r at n0))
  (def-adts $ (W : -> Type) enum (many MkW : (erased (MyNat) v) (unique (Placed (slot-of n0) (MyNat) v) p) -> (W)))
  (let ((unique w)) (MkW _ (place-at _ n0)))
  (let-match unique w (MkW _ p))
  (let-match erased (placed-slot _ _ _ p) (Refl _ _))
  (unplace-at _ _ _ p))
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique r)) (wrap-unwrap two))
(share r)
