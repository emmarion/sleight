; expect: 2
; `slot-self` (section 35): a `(Slot)` value read back out of data is made its own slot, so a cell whose
; type holds that slot can be filled `(at)` with the word it names.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Slot) s) -> (Box)))
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many fill : (many (Nat) n) (unique (Cell P (slot-of n) vacant-slot) u) -> (many (Nat) r))
  (let ((many bx)) (MkBox (slot-of n)))
  (let-match many bx (MkBox s _))
  (slot-self s)
  (let ((unique u2)) (cell-write u (P s _)))
  (let ((many p)) (u2 (at) n (Succ n)))
  (let-match many p (P x y _))
  y)
(let ((unique c)) (cell-alloc P))
(let ((many n)) 1)
(let ((unique c2)) (cell-write c (P (slot-of n) _)))
(fill n c2)
