; needs: ../std/macro macro_lib
; error: `numeral-of` takes a literal
(let ((erased nat-ty)) (Nat))
(let ((many nat-h)) (settled-of erased nat-ty))
(def-fns _ $ (many mint-numeral-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nat-h 3))
  (values mw1 $ one $ form here $ two (name here "numeral-of") (RawSettled here _ _ _ h)))
(let ((many numeral)) (MkMacro _ mint-numeral-fn))
(let ((erased p)) (numeral))
