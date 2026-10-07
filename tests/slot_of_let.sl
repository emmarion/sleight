; expect: 4
; A `let` binder of `(slot-of x)` sits where `x` does, a slot's word being the slot (AT_REDESIGN A2, A6), so
; no `slot-self` is needed to fill a cell at it.
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many n)) 4)
(let ((many s)) (slot-of n))
(let ((unique u)) (cell-alloc (P s _)))
(let ((many p)) (u (at) n n))
(let-match many p (P x y _))
x
