; error: type mismatch: expected `(Univ)`, got `(TyCtor ((Univ) A) -> Type)`
; error: hint: did you mean `(List _)`?
(def-fns _ $ (many f : (many List xs) -> (many (Nat) m))
  (Zero))
