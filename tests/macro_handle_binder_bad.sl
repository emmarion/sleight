; needs: macro_lib
; error: a handle to `k` is not a name
(let ((many k)) 1)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ form here $ three (name here "let") (form here $ one $ form here $ two (name here "many") (RawSettled here _ _ _ (settled-of many k))) (RawNat here 7)))
(let ((many m)) (MkMacro _ m-fn))
(m)
