; needs: list
; expect: (Cons (Zero) (Cons (Zero) (Nil)))
; A constructor application is a pure term, so its `_`s may stay open past its own paren: the argument after
; it in the same call, or in the enclosing constructor, solves them (SUGAR.md 6); a call is the boundary.

(def-lvl A)
(def-fns A $ many prepend : (erased Type X) (many (List X) front) (many (List X) xs) -> (many (List X) r)
  (match many front _
    ((Nil a) xs)
    ((Cons a hd tl) (Cons _ hd xs))))

(def-lvl B)
(def-fns B $ many twice : (many (List (Nat)) xs) -> (many (List (Nat)) r)
  (let (many one) (Cons _ (Zero) (Nil _)))
  (prepend _ (Nil _) (Cons _ (Zero) one)))

(twice (Nil (Nat)))
