; error: `cell-match` takes its cell at `many` or `unique`
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many run : -> (many (Nat) r))
  (let ((many a)) (Zero))
  (let ((unique u)) (cell-alloc P))
  (cell-match erased u (((Nat) r)) (P s t) a))
run
