(let ((many Func)) Fn)
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many (Nat) z)) inc)
(Zero)
; error: error: type mismatch: expected `(Nat)`, got `(Func (level-of inc) (many (Nat) n) -> (many (Nat) m))`
