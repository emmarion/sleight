; error: an at-match's annotation entries are erased or `at`
(def-fns _ $ (many same : (many (List (Nat)) xs) -> (many (List (Nat)) r))
  (match many xs (at (((List (Nat)) r)))
    ((Nil _ u) (at many (u _)))
    ((Cons _ hd tl u) (at many (u _ hd tl)))))
