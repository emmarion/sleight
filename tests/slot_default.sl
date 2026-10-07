; expect: 2
; A binder whose type is `(Slot)` is its own slot without `slot-self` (section 35, the
; owner's tentative reading): a word `at` an opaque `(Slot)` parameter is in the slot the parameter names.
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many fill : (many (Slot) s) (many (Nat) n at s) (unique (Cell P s vacant-slot) u) -> (many (Nat) r))
  (let ((many p)) (u (at) n (Succ n)))
  (let-match many p (P x y _))
  y)
(let ((unique c)) (cell-alloc P))
(let ((many n)) 1)
(let ((unique c2)) (cell-write c (P (slot-of n) _)))
(fill (slot-of n) n c2)
