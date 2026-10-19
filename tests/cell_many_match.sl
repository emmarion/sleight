; expect: (Cons _ 1 $ Cons _ 2 $ Nil _)
; A match at `many` gives a cell too (section 37), at `many`: a full-at reinvocation of it costs nothing and
; mints the value at `many`, the idiom of DESIGN.md section 23 without giving anything up.
(def-fns _ $ (many same : (many (List (Nat)) xs) -> (many (List (Nat)) r at xs))
  (match many xs _
    ((Nil _ u) (at many (u _)))
    ((Cons _ hd tl u) (at many (u _ hd tl)))))
(same (Cons _ 1 (Cons _ 2 (Nil _))))
