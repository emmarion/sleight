; expect: (MySucc $ MyZero)
; The placing primitives compile to renamings, as `coerce` does: an at-function's body may consist of them, and a
; tail call may be followed by one.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (many (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many at rebox : (erased (Slot) s) (erased (MyNat) v) (unique (Placed s (MyNat) v) b) ->
    (unique (Placed (slot-of b) (MyNat) v) b2 at b))
  (let ((unique x)) (unplace-at s _ v b))
  (place-at _ x))
(def-fns _ $ (many succ : (many (MyNat) n) -> (many (MyNat) r))
  (MySucc n))
(def-fns _ $ (many succ-placed : (many (MyNat) n) -> (many (MyNat) r) (many (Placed (slot-of r) (MyNat) r) p at r))
  (let ((many r)) (tail (succ n)))
  (values r (place-at-many _ r)))
(let ((many one) (many p)) (succ-placed (MyZero)))
(let ((unique b)) (place-at _ (MySucc (MyZero))))
(let ((unique b2)) (at erased (rebox _ _ b)))
(let ((unique x)) (unplace-at _ _ _ b2))
(share x)
