; An at-function's body is checked as if each `sorry` were a value: a call it binds is a call, tainted or not.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many at same : (many (Nat) n) -> (many (Nat) m at n))
  (let ((many _u)) (inc (sorry _)))
  n)
; error: tests/sorry_at_fn_bad.sl:4:14: error: the body of at-function `same` does not erase to nothing
