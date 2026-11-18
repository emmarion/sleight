(def-fns _ $ (many lb-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "t"))
  (match many (lt-dec k 10000) _
    ((Yes _ _ _ _ _) (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "lb")) $ Nil _) $ Nil _))
    ((No _ _ _ _ _) (values mw1 $ Cons _ (RawSymbol here (SName "Zero")) $ Nil _))))
(let ((many lb)) (MkMacro _ lb-fn))
(lb)
