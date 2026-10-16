(def-fns _ $ (many drop-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Zero")) (Nil _)) (Nil _)))
(let ((many drop)) (MkMacro _ drop-fn))
(def-fns _ $ (many boom-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "compile-error")) (Nil _)) (Nil _)))
(let ((many boom)) (MkMacro _ boom-fn))
(let ((many keep)) drop)
(MkPair _ _ (drop (boom)) (drop (drop (boom)) keep))
