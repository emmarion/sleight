; needs: list
; expect: (Zero)
; A match's _ annotation reuses an argument's expected type once that type is settled.
(def-lvl A)
(def-fns A $ many len : (erased Type X) (many (List X) xs) -> (many (Nat) n) (Zero))
(def-lvl B)
(def-fns B $ many g : (many (Nat) n) -> (many (Nat) m)
  (len (Nat) (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ k (Nil _))))))
(g (Succ (Zero)))
