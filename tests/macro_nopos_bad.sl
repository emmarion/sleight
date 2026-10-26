; needs: ../std/macro macro_lib
; error: expected `(Nat)`
(def-fns _ $ (many m : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many x)) (str-raw mw (NoPos) "x"))
  (values mw1 $ Cons _ (RawList (NoPos) $ Cons _ (RawSymbol (NoPos) (SName "Succ")) $ Cons _ x $ Nil _) $ Nil _))
(let ((many mac)) (MkMacro _ m))
(mac)
