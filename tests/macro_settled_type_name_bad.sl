; needs: ../std/macro macro_lib
; error: a handle to `_` is not a name
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many again-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "settled-of")) $ Cons _ (RawSymbol here (SName "erased")) $ Cons _ (RawSettled here _ _ _ (settled-type _ _ _ (settled-of many xs))) $ Nil _) $ Nil _))
(let ((many again)) (MkMacro _ again-fn))
(let ((many h)) (again))
