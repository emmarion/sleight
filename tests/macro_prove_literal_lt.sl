; needs: ../std/macro macro_lib
; expect: "ok"
(let ((many k)) 5)
(def-fns _ $ (many lt-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many nine)) (nat-raw mw here 9))
  (values mw1 $ one $ form here $ three (name here "prove-literal-lt") (RawSettled here _ _ _ (settled-of many k)) nine))
(let ((many lt)) (MkMacro _ lt-fn))
(let ((erased p)) (lt))
"ok"
