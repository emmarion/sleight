; needs: list
; expect: (Succ (Succ (Succ (Zero))))
; $ nests: each one runs to its enclosing form's close paren (section 2).

(def-fns _ $ many f : (many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (match many a (((Nat) r))
    ((Zero) b)
    ((Succ k) (Succ b))))

(f (Succ $ Zero) $ f (Zero) $ Succ $ Succ (Zero))
