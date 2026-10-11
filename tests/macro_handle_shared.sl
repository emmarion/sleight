; needs: macro_lib
; expect: (MkPair _ _ 1 2)
(let ((unique u)) (MkPair _ _ 1 2))
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ form here $ one $ RawSettled here _ _ _ (settled-of unique u)))
(let ((many sh)) (MkMacro _ m-fn))
(let ((many s)) (share u))
(def-fns _ $ (many n-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawSettled here _ _ _ (settled-of many s)))
(let ((many read)) (MkMacro _ n-fn))
(let ((many a)) (read))
(read)
