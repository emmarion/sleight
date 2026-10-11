; needs: macro_lib
; error: 7 is a literal, not a name
(def-fns _ $ (many bind-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (intern-nat mw 7))
  (values mw1 $ one $ form here $ three (name here "let") (form here $ one $ form here $ two (name here "many") (RawConst here _ _ _ h)) (RawNat here 1)))
(let ((many bind)) (MkMacro _ bind-fn))
(bind)
