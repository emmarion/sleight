; error: type mismatch: expected `(List (Nat))`, got `(ValCtor (erased Type A) -> (List A))`
; error: hint: did you mean `(Nil _)`?
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) a) (many (List (Nat)) b))
  (values n Nil))
