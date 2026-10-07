(def-fns _ $ (many f : (subterm many (List (Nat)) xs) (subterm many (List (Nat)) ys) -> (many (Nat) n))
  (let-match many xs (Cons _ h t) ((Nil _) 0))
  (f (subterm _) t (subterm _) ys))
; error: tests/msg_subterm_twice_bad.sl:3:20: error: a call carries at most one decrease annotation
