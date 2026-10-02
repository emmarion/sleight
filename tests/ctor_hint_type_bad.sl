; error: type mismatch: expected `Type`, got `(TyCtor (Type A) -> Type)`
; error: hint: did you mean `(List _)`?
(def-fns _ $ (many f : (many List xs) -> (many (Nat) m))
  (Zero))
