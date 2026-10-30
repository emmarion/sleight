; expect: (Cons _ 1 $ Cons _ 1 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 62 $ Nil _)
(def-fns _ $ (many below-8 : (many (Nat) n) -> (many (Nat) r))
  (let ((erased v) (erased p) (erased _)) (pow2 3))
  (match many (lt-pow2-dec n 3 v p) _ ((Yes _ _ _ _ _) 1) ((No _ _ _ _ _) 0)))
(def-fns _ $ (many below-1 : (many (Nat) n) -> (many (Nat) r))
  (let ((erased v) (erased p) (erased _)) (pow2 0))
  (match many (lt-pow2-dec n 0 v p) _ ((Yes _ _ _ _ _) 1) ((No _ _ _ _ _) 0)))
(def-fns _ $ (many lt-pow2-test : -> (many (List (Nat)) r))
  (Cons _ (below-8 0) $ Cons _ (below-8 6) $ Cons _ (below-8 7) $ Cons _ (below-8 8) $ Cons _ (below-8 9) $
    Cons _ (below-1 0) $ Cons _ (below-1 1) $ Cons _ (sixty-two-many) $ Nil _))
lt-pow2-test
