(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))

(def-fns _ $ (many fill : (many (Nat) n) (many (Nat) m) -> (many (Pair2) p))
  (let ((unique u)) (cell-alloc (P (slot-of n) _)))
  (share (u (at) m n)))

(fill 1 2)
