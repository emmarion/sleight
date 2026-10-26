; needs: ../std/macro macro_lib
; error: `numeral-of` takes a literal
(let ((erased nat-ty)) (Nat))
(let ((many nat-h)) (settled-of erased nat-ty))
(def-fns _ $ (many mint-numeral-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ nat-h 3))
  (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "numeral-of")) $ Cons _ (RawSettled here _ _ _ h) $ Nil _) $ Nil _))
(let ((many numeral)) (MkMacro _ mint-numeral-fn))
(let ((erased p)) (numeral))
