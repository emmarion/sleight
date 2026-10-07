; expect: 2
; `slot-self` (section 35): a `(Slot)` parameter made its own slot, so a word `at` it is in the slot it
; names; without the `slot-self` this is `tests/slot_default_bad.sl`.
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many fill : (many (Slot) s) (many (Nat) n at s) (unique (Cell P s vacant-slot) u) -> (many (Nat) r))
  (slot-self s)
  (let ((many p)) (u (at) n (Succ n)))
  (let-match many p (P x y _))
  y)
(let ((unique c)) (cell-alloc P))
(let ((many n)) 1)
(let ((unique c2)) (cell-write c (P (slot-of n) _)))
(fill (slot-of n) n c2)
