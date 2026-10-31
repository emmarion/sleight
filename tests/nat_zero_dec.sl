; expect: (Cons _ 0 $ Cons _ 1 $ Cons _ 1 $ Nil _)

(def-fns _ $ (many sign : (many (Nat) n) -> (many (Nat) r))
  (let-match many (nat-zero-dec n) (IsSucc m)
    ((IsZero) (let ((many (Zero) is z)) n) 0))
  (let ((many (Succ m) is s)) n)
  1)

(Cons _ (sign 0) $ Cons _ (sign 5) $ Cons _ (sign 1000) $ Nil _)
