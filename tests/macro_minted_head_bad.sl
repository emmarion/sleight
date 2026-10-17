; needs: ../std/macro macro_lib macro_mint_lib
(def-fns _ $ (many head-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nats-h (Nil _)))
  (values mw1 $ one $ form here $ one $ RawSettled here _ _ _ h))
(let ((many minted-head)) (MkMacro _ head-fn))
(minted-head)
; error: tests/macro_minted_head_bad.sl:7:1: error: `__1` : `(List (Nat))` is not applicable
