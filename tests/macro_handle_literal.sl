; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 3 "s")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many f) (many g)) (values 3 "s"))
  (values mw $ one $ form here $ Cons _ (name here "MkPair") $ Cons _ (RawWild here) $ three (RawWild here) (RawSettled here _ _ _ (settled-of many f)) (RawSettled here _ _ _ (settled-of many g))))
(let ((many lits)) (MkMacro _ m-fn))
(lits)
; warn-unused: no
