; A function's level is part of its type, so a function at a level made by `sorry` is tainted.
(let ((erased l)) (sorry (((Level) x))))
(def-fns l $ (many f : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many g : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(g 1)
;! file "sorry/level.sl"
(f 1)
; expect: 2
; expect: sorry
; warns: tests/sorry_level.sl:2:19: warning: this unit uses `sorry` once, here; nothing that depends on it runs
