; error: return does not satisfy `at`
; tests/placed_thread.sl's `go` without the `placed-slot`: the box's index is not yet the slot of the box.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many go : (unique (MyNat) n) (erased (MyNat) w) (unique (Placed (slot-of n) (MyNat) w) b) -> (unique (MyNat) r at n))
  (unplace-at (slot-of n) _ w b))
