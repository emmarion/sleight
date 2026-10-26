; needs: ../std/macro macro_lib
; expect: (MkPair _ _ "erased many" $ MkPair _ _ 1 2)
(let ((unique u)) (MkPair _ _ 1 2))
(let ((many k)) 5)
(def-fns _ $ (many mult-name : (many (Mult) m) -> (many (String) s))
  (match many m _ ((MErased) "erased") ((MMany) "many") ((MUnique) "unique")))
(def-fns _ $ (many mention-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "let")) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "erased")) $ Cons _ (RawSymbol here (SName "e")) $ Nil _) $ Nil _) $ Cons _ (RawSettled here _ _ _ (settled-erase _ _ _ (settled-of unique u))) $ Nil _) $ Nil _))
(let ((many mention)) (MkMacro _ mention-fn))
(mention)
(let ((many names)) (str-append (mult-name $ settled-mult _ _ _ (settled-erase _ _ _ (settled-of many k))) $ str-append " " (mult-name $ settled-mult _ _ _ (settled-of many k))))
(MkPair _ _ names (share u))
