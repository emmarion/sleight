; needs: ../std/macro macro_lib macro_mint_lib
; error: type mismatch
(def-fns _ $ (many bad-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nats-h 3))
  (values mw1 $ one $ RawSettled here _ _ _ h))
