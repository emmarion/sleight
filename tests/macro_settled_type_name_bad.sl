; needs: macro_lib
; error: a handle to `_` is not a name
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many again-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ form here $ three (name here "settled-of") (name here "erased") (RawSettled here _ _ _ (settled-type _ _ _ (settled-of many xs)))))
(let ((many again)) (MkMacro _ again-fn))
(let ((many h)) (again))
