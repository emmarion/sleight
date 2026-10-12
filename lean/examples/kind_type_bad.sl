; a type is erased by its kind (DESIGN.md section 14), so it cannot be passed for a many parameter
(def-fns _ $ (many f : (erased Type A) (many A x) -> (many A y))
  x)
(f Type (Nat))
