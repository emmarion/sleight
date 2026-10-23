; needs: ../std/macro macro_lib
; error: 1 is a literal, not a name
(let ((many k)) 1)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw9) (many lit)) (nat-raw mw here 7))
  (values mw9 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "let")) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "many")) $ Cons _ (RawSettled here _ _ _ (settled-of many k)) $ Nil _) $ Nil _) $ Cons _ lit $ Nil _) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
