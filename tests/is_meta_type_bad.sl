; error: argument 2, `x`, of `g`: type mismatch: expected `(False)`, got `(Nat)`
; A `_` for an `is`-typed parameter is solved by the value alone; the type of the `is` expression still holds.
(def-fns _ $ (many g : (erased (False) j) (many j is x) -> (many (False) r)) x)
(def-fns _ $ (many absurd boom : (many (False) f) -> (many (Nat) n)) f)
(boom (g _ 3))
