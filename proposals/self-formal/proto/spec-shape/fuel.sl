(def-fns _ $ (many build : (subterm many (List (Nat)) xs) -> (many (Nat) r))
  (match many xs _ ((Nil _) (Zero)) ((Cons _ h t) (Succ $ build t))))
(let ((many r)) (build (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Nil _)))
r
