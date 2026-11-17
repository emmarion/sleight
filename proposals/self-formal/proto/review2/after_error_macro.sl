(compile-error "first")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSymbol here (SName "Zero")) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
