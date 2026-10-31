; error: expected a field name, got `(Nil _)`
(def-fns _ $ (many f : (many (List (Nat)) x) -> (many (Nat) r))
  (match many x _ ((Nil _) 0) ((Cons _ h (Nil _)) 1)))
f
