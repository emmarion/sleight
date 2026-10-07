; error: expects 3 or 4 binders, got 5
(def-fns _ $ (many len : (subterm unique (List (Nat)) xs) -> (many (Nat) n))
  (match unique xs _
    ((Nil _) 0)
    ((Cons _ hd tl u v) (Succ (len tl)))))
(len (Nil _))
