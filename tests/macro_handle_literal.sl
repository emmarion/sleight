; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 3 "s")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many f) (many g)) (values 3 "s"))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "MkPair")) $ Cons _ (RawWild here) $ Cons _ (RawWild here) $ Cons _ (RawSettled here _ _ _ (settled-of many f)) $ Cons _ (RawSettled here _ _ _ (settled-of many g)) $ Nil _) $ Nil _))
(let ((many lits)) (MkMacro _ m-fn))
(lits)
