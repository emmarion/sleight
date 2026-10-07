(def-fns _ $ (many f : (many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs (at _)
    ((Nil _) 0)
    ((Cons _ h t) h)))
; error: tests/msg_at_match_hole_bad.sl:2:22: error: an at-match's annotation is written out; `_` cannot stand for it
