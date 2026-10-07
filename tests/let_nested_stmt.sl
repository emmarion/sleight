; expect: 2
; A run-position let whose right-hand side carries its own statements: those run first, and its code runs
; in the scope they leave behind (section 27).

(let ((many two))
  (let ((many one)) (Succ (Zero)))
  (def-lvl X)
  (def-fns X $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
  (inc one))
two
