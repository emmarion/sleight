; expect: (MySucc $ MySucc $ MySucc $ MyZero)
; A parameter boxed by `place-at` travels through `bump`, whose signature names only the erased slot index;
; `placed-slot` turns the index back into the slot of the box, so `go` returns its result `at n`.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many bump : (erased (Slot) s) (erased (MyNat) v) (unique (Placed s (MyNat) v) b) ->
    (erased (MyNat) w) (unique (Placed s (MyNat) w) b2))
  (let ((unique m)) (unplace-at s _ v b))
  (let-match erased (placed-slot s _ v b) (Refl _ _))
  (let ((unique m2)) (match unique m (((MyNat) k at m))
    ((MyZero u) (u))
    ((MySucc q u) (u (MySucc q)))))
  (values m2 (place-at _ m2)))
(def-fns _ $ (many go : (unique (MyNat) n) -> (unique (MyNat) r at n))
  (let ((unique b)) (place-at _ n))
  (let ((erased w) (unique b2)) (bump (slot-of n) n b))
  (let ((unique m)) (unplace-at (slot-of n) _ w b2))
  (let-match erased (placed-slot (slot-of n) _ w b2) (Refl _ _))
  m)
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique r)) (go two))
(share r)
