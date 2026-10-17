; error: a `cell-write` written `unique` in an erased position; write `erased` here
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(let ((many n)) 1)
(let ((unique u)) (cell-alloc MkBox))
(let ((erased e)) (cell-write unique u (MkBox (slot-of n))))
(Zero)
