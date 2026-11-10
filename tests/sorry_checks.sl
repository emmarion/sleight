; What is checked of the code that runs is checked as if each `sorry` were a value: a `notail` call followed by
; a `let` of a tainted call is not in tail position, as it would not be were `t` a number, and an at-function
; whose body binds a tainted call is refused, or not, as it would be.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many t)) (sorry (((Nat) q))))
  (let ((many r)) (notail (inc n)))
  (let ((many _u)) (inc t))
  r)
(def-fns _ $ (many at same : (many (Nat) n) -> (many (Nat) m at n))
  (let ((erased _p)) (sorry (((Lt 1 2) q))))
  n)
(f (same 1))
; expect: 2
; warns: tests/sorry_checks.sl:7:19: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
