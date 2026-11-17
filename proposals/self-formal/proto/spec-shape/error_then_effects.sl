(compile-error "first")
(compile-warn "after")
(def-fns _ $ (many loop-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "loop")) $ Nil _) $ Nil _))
(let ((many loop)) (MkMacro _ loop-fn))
(loop)
