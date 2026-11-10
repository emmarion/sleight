; A `tail` claim is checked as if each `sorry` were a value: the `let` of a tainted call after the marked call
; leaves no code to run, and still keeps the call out of tail position.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many t)) (sorry (((Nat) q))))
  (let ((many r)) (tail (inc n)))
  (let ((many _u)) (inc t))
  r)
; error: tests/sorry_tail_bad.sl:5:14: error: a `tail`-marked call is not in tail position
