; externs: only
; expect: (Cons _ 1 $ Cons _ 1 $ Nil _)

(def-fns _ $ (many sign : (many (Nat) n) -> (many (Nat) r))
  (let-match many (nat-zero-dec n) (IsSucc m)
    ((IsZero) (let ((many (Zero) is _)) n) 0))
  (let ((many (Succ m) is _)) n)
  1)

(Cons _ (sign 4611686018427387904) $ Cons _ (sign 123456789012345678901234567890) $ Nil _)
