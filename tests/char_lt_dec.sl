; expect: (Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Nil _)
(let ((erased cg)) (coercible-of (delegate-of char-lt-dec)))

(let ((many d)) (char-lt-dec #\a #\b))
(comptime-match many d (Yes _ _ _ _ p))

(def-fns _ $ (many below : (many (Char) a) (many (Char) b) -> (many (Nat) r))
  (match many (char-lt-dec a b) _ ((Yes _ _ _ _ _) 1) ((No _ _ _ _ _) 0)))

(def-fns _ $ (many go : -> (many (List (Nat)) r))
  (Cons _ (below #\a #\b) $ Cons _ (below #\a #\a) $ Cons _ (below #\b #\a) $ Nil _))
go
