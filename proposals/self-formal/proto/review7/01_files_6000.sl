(def-fns _ $ (many la-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "t"))
  (match many (lt-dec k 6000) _
    ((Yes _ _ _ _ _) (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "la")) $ Nil _) $ Nil _))
    ((No _ _ _ _ _) (values mw1 $ Cons _ (RawSymbol here (SName "Zero")) $ Nil _))))
(let ((many la)) (MkMacro _ la-fn))
(la)
