; expect: 1
; The cell binder is optional at `unique` as at `many`: a pattern without it binds no cell.
(def-fns _ $ (many head : (unique (List (Nat)) xs) -> (many (Nat) n))
  (match unique xs _
    ((Nil _) 0)
    ((Cons _ hd tl) hd)))
(head (Cons _ 1 (Cons _ 2 (Nil _))))
