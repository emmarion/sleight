; needs: ../std/macro macro_lib
; expect: "distinct"
(let ((erased nat-ty)) (Nat))
(let ((many nat-h)) (settled-of erased nat-ty))
(def-fns _ $ (many twice-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many a)) (mint-settled mw _ nat-h 3))
  (let ((unique mw2) (many b)) (mint-settled mw1 _ nat-h 3))
  (let ((unique mw3) (many e)) (settled-eq _ _ _ _ _ _ mw2 a b))
  (let ((unique mw4) (many s)) (str-raw mw3 here $ match many e (((String) t)) ((Some _ _) "equal") ((None _) "distinct")))
  (values mw4 $ one s))
(let ((many twice)) (MkMacro _ twice-fn))
(twice)
