; expect: (MkPair _ _ (RawList (MkPos "f" 0 2) $ Cons _ (RawName (NoPos) "x") $ Nil _) $ MkPair _ _ "y" $ MkPos "f" 0 2)
(let ((many x)) (RawList (MkPos "f" 0 2) $ Cons _ (RawName (NoPos) "x") $ Nil _))
(def-fns _ $ (many first : (subterm many (Raw) r) -> (many (String) s))
  (let-match many r (RawList _ items) ((RawName _ t) t) (else "other"))
  (match many items _ ((Nil _) "none") ((Cons _ h _) (tail $ first h))))
(def-fns _ $ (many pos : (many (Raw) r) -> (many (Pos) p))
  (match many r _ ((RawName p _) p) ((RawList p _) p) ((RawNat p _) p) ((RawChar p _) p) ((RawStr p _) p) ((RawWild p) p) ((RawGen p _ _ _) p)))
(def-fns _ $ (many main : -> (many (Pair (Raw) $ Pair (String) (Pos)) p)) (MkPair _ _ x $ MkPair _ _ (first $ RawList (NoPos) $ Cons _ (RawName (NoPos) "y") $ Cons _ x $ Nil _) (pos x)))
main
