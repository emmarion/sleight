(let ((many Func)) Fn)
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many (Nat) z)) inc)
(Zero)
; error: error: type mismatch: expected `(Nat)`, got `(Func _1 (many (Nat) n) -> (many (Nat) m))`
; error: tests/keyword_synonym_bad.sl:2:10: note: `_1` is anonymous, minted here
