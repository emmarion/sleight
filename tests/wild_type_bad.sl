; needs: list
; error: cannot infer the `_` in `(List ?1)`
; A type constructor application has nothing to solve its _ from where no is-expectation reaches it.
(def-lvl A)
(def-fns A $ (many f : (many (List _) xs) -> (many (Nat) n)) (Zero))
(f (Nil (Nat)))
