(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "BFalse")) $ Nil _) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(compile-error "first")
(let ((many x)) (m))
(comptime-match many x (BFalse))
(compile-warn "end")
