(def-adts $ (T : -> Type) enum (many A : (many (Nat) n) -> (T)) (many B : (many (String) s) (many (String) t) -> (T)))
(def-fns _ $ (many f : (unique (T) x) -> (unique (T) r at x))
  (let-match unique x (A n u) ((B s t u2) (u2 s t)))
  (let ((unique u3)) (cell-write unique u (B _ _)))
  (u3 "p" "q"))
(share (f (A 1)))
; error: tests/msg_cell_write_ctor_bad.sl:4:22: error: value mismatch: expected `A`, got `B`
