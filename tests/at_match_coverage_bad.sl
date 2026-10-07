; error: this `match` is missing a branch for the following unrefuted constructor
(def-fns _ $ (many same : (many (List (Nat)) xs) -> (many (List (Nat)) r at xs))
  (match many xs (at (((List (Nat)) r at xs)))
    ((Nil _ u) (at (u _)))))
