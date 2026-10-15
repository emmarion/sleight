(def-fns _ $ (many succ-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Succ")) args) (Nil _)))
(let ((many inc)) (MkMacro _ succ-fn))
(inc (inc 2))
