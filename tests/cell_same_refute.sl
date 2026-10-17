; expect: 0
(def-fns _ $ (many run : (many (List (Nat)) xs) -> (many (Nat) out))
  (let-match many xs (Cons _ _ t uc) ((Nil _) 2))
  (let-match many t (Nil _ un) ((Cons _ _ _) 3))
  (let-match many (slot-eq (slot-of un) (slot-of uc)) (Some _ e) ((None _) 0))
  (let-match erased e (Refl _ _))
  (let-match many (cell-same un uc) (EONonErased _ j) ((EOErased _) 1))
  (match erased j (((Nat) r))))
(run (Cons _ 5 (Nil _)))
; warns: tests/cell_same_refute.sl:8:3: warning: a non-erased `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function `absurd` instead
