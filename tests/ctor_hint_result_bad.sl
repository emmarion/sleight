; error: type mismatch: expected `(List (Nat))`, got `(ValCtor (erased (Univ) A) -> (List A))`
; error: hint: did you mean `(Nil _)`?
(def-fns _ $ (many f : (many (Nat) n) -> (many (List (Nat)) m))
  Nil)
