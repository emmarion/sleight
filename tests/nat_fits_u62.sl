; expect: (Cons _ 1 $ Cons _ 1 $ Nil _)

(def-fns _ $ (many fits : (many (Nat) n) -> (many (Nat) r))
  (match many (nat-fits-u62 n) _ ((Yes _ _ _ _ _) 1) ((No _ _ _ _ _) 0)))

(Cons _ (fits 0) $ Cons _ (fits 5) $ Nil _)
