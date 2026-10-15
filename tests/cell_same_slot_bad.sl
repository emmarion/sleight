; error: `u1` and `u2` are not at one slot
(def-fns _ $ (many f : (many (List (Nat)) xs) (many (List (Nat)) ys) -> (many (ErasedOr (Unit)) r))
  (let-match many xs (Cons _ h1 t1 u1) ((Nil _) (EONonErased _ (MkUnit))))
  (let-match many ys (Cons _ h2 t2 u2) ((Nil _) (EONonErased _ (MkUnit))))
  (let ((many s)) (cell-same u1 u2))
  (EONonErased _ (MkUnit)))
