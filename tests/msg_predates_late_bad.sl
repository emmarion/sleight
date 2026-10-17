(def-fns _ $ (many g : (many (Nat) x) (many (Nat) _y) -> (many (Nat) n)) x)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) n))
  (g x (predates _) x))
; error: tests/msg_predates_late_bad.sl:3:8: error: `predates` is written immediately after the callee
