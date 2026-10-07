(def-fns _ $ (many g : (many (Nat) x) -> (many (Nat) n)) x)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) n))
  (g (predates _) (predates _) x))
; error: tests/msg_decrease_twice_bad.sl:3:19: error: a call carries at most one decrease annotation
