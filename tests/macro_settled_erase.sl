; needs: macro_lib
; expect: (MkPair _ _ "erased many" $ MkPair _ _ 1 2)
(let ((unique u)) (MkPair _ _ 1 2))
(let ((many k)) 5)
(def-fns _ $ (many mult-name : (many (Mult) m) -> (many (String) s))
  (match many m _ ((MErased) "erased") ((MMany) "many") ((MUnique) "unique")))
(def-fns _ $ (many mention-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ form here $ three (name here "let") (form here $ one $ form here $ two (name here "erased") (name here "e"))
    (RawSettled here _ _ _ (settled-erase _ _ _ (settled-of unique u)))))
(let ((many mention)) (MkMacro _ mention-fn))
(mention)
(let ((many names)) (str-append (mult-name $ settled-mult _ _ _ (settled-erase _ _ _ (settled-of many k))) $ str-append " " (mult-name $ settled-mult _ _ _ (settled-of many k))))
(MkPair _ _ names (share u))
