; error: type mismatch: expected `(Univ)`, got `(TyCtor -> Type)`
; error: hint: did you mean `((pick 1))`?
(def-fns _ $ (erased pick : (many (Nat) b) -> (erased (TyCtor -> Type) t))
  Nat)
(def-fns _ $ (many k : (erased Type A) -> (many (Nat) m))
  (Zero))
(k (pick 1))
