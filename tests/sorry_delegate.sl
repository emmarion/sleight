; A `delegate` call that is tainted leaves no call behind; the function is tainted rather than refused.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-lvl V)
(def-fns V $ (many inc2 at inc : (many (Nat) _n) -> (many (Nat) m))
  (delegate (inc (sorry _))))
(MkPair (Nat) (Nat) (inc 1) (inc2 3))
; expect: sorry
; warns: tests/sorry_delegate.sl:6:18: warning: this unit uses `sorry` once, here; nothing that depends on it runs
