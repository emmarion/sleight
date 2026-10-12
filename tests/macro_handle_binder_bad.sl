; needs: ../std/macro macro_lib
; error: 1 is a literal, not a name
(let ((many k)) 1)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw9) (many lit)) (nat-raw mw here 7))
  (values mw9 $ one $ form here $ three (name here "let") (form here $ one $ form here $ two (name here "many") (RawSettled here _ _ _ (settled-of many k))) lit))
(let ((many m)) (MkMacro _ m-fn))
(m)
