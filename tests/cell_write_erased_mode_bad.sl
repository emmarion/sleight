; error: `cell-write` takes its cell at `many` or `unique` in a non-erased position
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(let ((many n)) 1)
(let ((unique u)) (cell-alloc MkBox))
(let ((unique u2)) (cell-write erased u (MkBox (slot-of n))))
(Zero)
