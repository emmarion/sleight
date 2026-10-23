; needs: ../std/macro macro_lib macro_mint_lib
; expect: (Cons _ 4 $ Cons _ 8 $ Nil _)
(def-fns _ $ (many reread-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nats-h (Cons _ 4 $ Cons _ 8 $ Nil _)))
  (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "settled-value")) $ Cons _ (RawWild here) $ Cons _ (RawWild here) $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "settled-of")) $ Cons _ (RawSymbol here (SName "many")) $ Cons _ (RawSettled here _ _ _ h) $ Nil _) $ Nil _) $ Nil _))
(let ((many reread)) (MkMacro _ reread-fn))
(reread)
