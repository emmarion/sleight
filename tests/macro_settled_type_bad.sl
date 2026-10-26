; needs: ../std/macro macro_lib
; error: type mismatch: expected `(List (Nat))`, got `(Nat)`
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many typed-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw9) (many lit)) (nat-raw mw here 3))
  (values mw9 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "let")) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "many")) $ Cons _ (RawSettled here _ _ _ (settled-type _ _ _ (settled-of many xs))) $ Cons _ (RawSymbol here (SName "n")) $ Nil _) $ Nil _) $ Cons _ lit $ Nil _) $ Nil _))
(let ((many typed)) (MkMacro _ typed-fn))
(typed)
