; expect: _
; `placed-eq` equates two boxes whose indices agree, so a proof about one carries to the other; a box prints `_`.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (many (MyNat) pred) -> (MyNat)))
(def-adts $ (Mine : (Type A) (A a) -> Type) enum (many MkMine : (erased Type A) (erased A a) -> (Mine A a)))
(def-fns _ $ (many carry : (erased (Slot) s) (erased (MyNat) v) (many (Placed s (MyNat) v) _p) (erased (Placed s (MyNat) v) q)
    (erased (Mine (Placed s (MyNat) v) _p) m) -> (erased (Mine (Placed s (MyNat) v) q) m2))
  (let-match erased (placed-eq s _ v _p q) (Refl _ _))
  m)
(let ((many x)) (MySucc (MyZero)))
(let ((many p)) (place-at-many _ x))
(let ((erased q)) (place-at-many _ x))
(let ((erased m2)) (carry _ _ p q (MkMine _ p)))
p
