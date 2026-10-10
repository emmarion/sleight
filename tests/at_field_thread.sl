; expect: (MySucc $ MySucc $ MySucc $ MyZero)
; A field written `at` a `(Slot)` sibling (section 36). The world `n` enters a state block as the word of its
; slot field; `step`'s signature says nothing about where anything sits and returns a fresh block; the holder
; of `n` gets the world back `at n` from the index alone, through `slot-self` on the slot the destructure binds.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(def-fns _ $ (many step : (erased (Slot) s) (unique (State s) st) -> (unique (State s) st2))
  (let-match unique st (MkState s2 n k))
  (let-match unique n (MySucc p u2)
    ((MyZero u0) (MkState s2 (u0) k)))
  (MkState s2 (u2 (MySucc p)) k))
(def-fns _ $ (many bump : (unique (MyNat) n) -> (unique (MyNat) r at n))
  (let ((unique st)) (MkState (slot-of n) n 0))
  (let ((unique st2)) (step _ st))
  (let-match unique st2 (MkState s n2 k))
  (slot-self s)
  n2)
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique r)) (bump two))
(share r)
