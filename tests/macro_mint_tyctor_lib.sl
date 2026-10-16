; needs: ../std/macro
(let ((erased tyctor-type)) (TyCtor (Type A) -> Type))
(let ((many tyctor-h)) (settled-of erased tyctor-type))
(def-fns _ $ (many opaque-list-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled-erased mw _ tyctor-h List))
  (values mw1 $ one $ form here $ Cons _ (RawSettled here _ _ _ h) args))
(let ((many opaque-list)) (MkMacro _ opaque-list-fn))
