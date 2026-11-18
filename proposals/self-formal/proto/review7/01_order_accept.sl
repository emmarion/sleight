(def-fns _ $ (many gs-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "t"))
  (let ((unique mw2) (many h)) (intern-nat mw1 k))
  (values mw2 $ Cons _ (RawSettled here _ _ _ h) $ Nil _))
(let ((many gs)) (MkMacro _ gs-fn))
(def-fns _ $ (many first-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "t"))
  (match many (lt-dec k 2) _
    ((Yes _ _ _ _ _) (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Zero")) $ Nil _) $ Nil _))
    ((No _ _ _ _ _) (values mw1 $ Cons _ (RawSymbol here (SName "not-first")) $ Nil _))))
(let ((many first-only)) (MkMacro _ first-fn))
(MkPair _ _ (MkPair _ _ (gs) (gs)) (first-only))
