; externs: only
; expect: (Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 4611686018427387903 $ Nil _)

(def-fns _ $ (many fits : (many (Nat) n) -> (many (Nat) r))
  (match many (nat-fits-u62 n) _ ((Yes _ _ _ _ _) 1) ((No _ _ _ _ _) 0)))

(def-fns _ $ (many top-or-zero : (many (Nat) n) -> (many (Nat) r))
  (match many (nat-fits-u62 n) _ ((Yes _ _ _ _ p) (u62-add n (Zero) n (add-zero-right n) p)) ((No _ _ _ _ _) 0)))

(Cons _ (fits 4611686018427387903) $ Cons _ (fits 4611686018427387904) $ Cons _ (fits (nat-shl 1 100)) $ Cons _ (top-or-zero 4611686018427387903) $ Nil _)
