; error: 7 is not a statement
; error: hint: every item of a body but the last must be a statement
(def-fns _ $ (many f : -> (many (Nat) y))
  7
  42)
