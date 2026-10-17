; needs: ../std/macro macro_lib
; error: expected `(Nat)`
(def-fns _ $ (many m : (unique (MacroWorld) mw) (many (Pos) _here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many x)) (str-raw mw (NoPos) "x"))
  (values mw1 $ one $ RawList (NoPos) $ Cons _ (name (NoPos) "Succ") $ Cons _ x $ Nil _))
(let ((many mac)) (MkMacro _ m))
(mac)
