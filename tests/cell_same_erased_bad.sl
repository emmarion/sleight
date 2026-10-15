; error: `cell-same` in an erased position
(def-fns _ $ (many f : (many (List (Nat)) xs) -> (many (Nat) r))
  (let-match many xs (Cons _ h t u) ((Nil _) 0))
  (let ((erased s)) (cell-same u u))
  0)
