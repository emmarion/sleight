; expect: (MkPair _ _ 1 7)
; A `cell-write` on a cell at `many` copies (section 37): the shared block is untouched, the new cell is
; unique and at nothing, and an all-`_` write is how a shared block becomes a unique one.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many bump : (many (Box) b) -> (many (Pair (Nat) (Nat)) r))
  (let-match many b (MkBox _ u))
  (let ((unique u2)) (cell-write many u (MkBox _)))
  (let ((many fresh)) (share (u2 7)))
  (let-match many fresh (MkBox m))
  (let-match many b (MkBox k))
  (MkPair _ _ k m))
(bump (MkBox 1))
