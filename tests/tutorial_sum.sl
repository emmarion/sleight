; expect: 6
(def-fns _ $ (many sum : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) 0)
    ((Cons _ hd tl) (nat-add hd $ notail $ sum tl))))

(sum $ Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil (Nat))
