; error: type mismatch: expected `(List (Nat))`, got `(ValCtor (erased Type A) -> (List A))`
; error: hint: did you mean `(Nil _)`?
(let ((many (Nat) n) (many (List (Nat)) xs)) (values 1 Nil))
xs
