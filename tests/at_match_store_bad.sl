; error: a branch of an at-match must erase to nothing, or to a reordering of variables; this one stores, allocates or calls
(def-fns _ $ (many same : (many (List (Nat)) xs) -> (many (List (Nat)) r at xs))
  (match many xs (at (((List (Nat)) r at xs)))
    ((Nil _ u) (at many (u _)))
    ((Cons _ hd tl u) (let ((many y)) (Succ hd)) (at many (u _ hd tl)))))
