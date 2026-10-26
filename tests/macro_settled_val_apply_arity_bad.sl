; error: `MkPair` expects 4 arguments, got 5
; needs: ../std/macro
(let ((many k)) 3)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many _)) (settled-val-apply mw (settled-of many MkPair) (settled-of erased nat-type) (settled-of erased nat-type) (settled-of many k) (settled-of many k) (settled-of many k)))
  (values mw1 (Nil _)))
