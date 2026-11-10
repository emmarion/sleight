; A `delegate` body is checked as it would be with a value in place of the `sorry`: an argument that is one is
; computed before the call, as any argument that is not a variable is.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-lvl V)
(def-fns V $ (many inc2 at inc : (many (Nat) _n) -> (many (Nat) m))
  (delegate (inc (sorry _))))
; error: tests/sorry_delegate_bad.sl:6:14: error: a `delegate`-marked call is not in tail position
