; error: `u1` and `u2` are not at one slot
(def-fns _ $ (many heads : (many (List (Nat)) xs) (many (List (Nat)) ys) -> (many (Nat) r))
  (let-match many xs (Cons _ h1 t1 u1) ((Nil _) 0))
  (let-match many ys (Cons _ h2 t2 u2) ((Nil _) 0))
  (match many (slot-eq (slot-of u1) (slot-of u2)) _
    ((Some _ e) 0)
    ((None _) (let-match many (cell-same u1 u2) (EONonErased _ j) ((EOErased _) 0)) 1)))
