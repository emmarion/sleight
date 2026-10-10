; error: type mismatch: expected `(List (Nat))`, got `(List (Bool))`
; A literal first met inside a body, then a type error at the top level, whose message names the terms of a
; scope that never met the literal.
(def-fns _ $ (many f : -> (many (Nat) n))
  42)
(let ((many x)) (Cons (Nat) 7 (Nil (Bool))))
