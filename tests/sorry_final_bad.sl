; A tainted final value is checked as its type would be with a value: a function in neither of the driver's
; forms is refused, though nothing of it would run.
(def-fns _ $ (many g : (many (Nat) n) -> (many (Nat) m))
  n)
(let ((many h)) (sorry (((Fn (level-of g) (many (Nat) n) -> (many (Nat) m)) q))))
h
; error: tests/sorry_final_bad.sl:6:1: error: a final function must be
