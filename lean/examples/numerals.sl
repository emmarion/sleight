; numerals (DESIGN.md section 45): opaque Nat entries, printed back as numerals
(def-fns _ $ (many pred : (many (Nat) n) -> (many (Nat) m))
  (match many n _
    ((Zero) 0)
    ((Succ k) k)))
(def-fns _ $ (many main : -> (many (List (Nat)) xs))
  (Cons _ 3 $ Cons _ (pred 3) $ Cons _ (pred 0) $ Nil _))
main
