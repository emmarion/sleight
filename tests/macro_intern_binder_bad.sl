; needs: ../std/macro macro_lib
; error: 7 is a literal, not a name
(def-fns _ $ (many bind-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (intern-nat mw 7))
  (let ((unique mw9) (many lit)) (nat-raw mw1 here 1))
  (values mw9 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "let")) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "many")) $ Cons _ (RawSettled here _ _ _ h) $ Nil _) $ Nil _) $ Cons _ lit $ Nil _) $ Nil _))
(let ((many bind)) (MkMacro _ bind-fn))
(bind)
