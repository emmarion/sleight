; expect: (MkPair _ _ 1 2)
(let ((unique u)) (MkPair _ _ 1 2))
(let ((unique k)) u)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ (settled-of unique k)) $ Nil _))
(let ((many take)) (MkMacro _ m-fn))
(let ((unique a)) (take))
(share a)
