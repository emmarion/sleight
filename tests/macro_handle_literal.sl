; needs: macro_lib
; expect: (MkPair _ _ 3 "s")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many f) (many g)) (values 3 "s"))
  (values mw $ one $ form here $ Cons _ (name here "MkPair") $ Cons _ (RawWild here) $ three (RawWild here) (RawConst here _ _ _ (constant-of many f)) (RawConst here _ _ _ (constant-of many g))))
(let ((many lits)) (MkMacro _ m-fn))
(lits)
