; needs: list
; error: the telescope `_` would reuse still has a `_` to infer
(def-lvl A)
(def-fns A $ (many len : (erased Type X) (many (List X) xs) -> (many (Nat) n)) (Zero))
(def-fns A $ (many g : (many (Nat) n) -> (many (Nat) m))
  (len _ (match many n _ ((Zero) (Nil (Nat))) ((Succ k) (Nil (Nat))))))
(g (Zero))
