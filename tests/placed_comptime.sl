; expect: (MySucc $ MyZero)
; `comptime-match` binds a `Placed` field as a Settled value, which `unplace-at` takes back in run position.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (erased (Slot) s) (erased (MyNat) v) (unique (Placed s (MyNat) v) n) (many (Nat) steps) -> (State s)))
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique st)) (MkState _ _ (place-at _ two) 0))
(comptime-match unique st (MkState s v n k u))
(let ((unique m)) (unplace-at _ _ _ n))
(let-match unique m (MySucc p))
(share p)
