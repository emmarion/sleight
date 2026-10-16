; needs: ../std/macro macro_lib macro_mint_lib
; expect: (Cons _ 4 $ Cons _ 8 $ Nil _)
(def-fns _ $ (many reread-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nats-h (Cons _ 4 $ Cons _ 8 $ Nil _)))
  (values mw1 $ one $ form here $ Cons _ (name here "settled-value") $ Cons _ (RawWild here) $ Cons _ (RawWild here) $ one $
    form here $ three (name here "settled-of") (name here "many") (RawSettled here _ _ _ h)))
(let ((many reread)) (MkMacro _ reread-fn))
(reread)
