; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 1 2)
(let ((unique u)) (MkPair _ _ 1 2))
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of unique u)) $ Nil _) $ Nil _))
(let ((many sh)) (MkMacro _ m-fn))
(let ((many s)) (share u))
(def-fns _ $ (many n-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ (settled-of many s)) $ Nil _))
(let ((many read)) (MkMacro _ n-fn))
(let ((many a)) (read))
(read)
