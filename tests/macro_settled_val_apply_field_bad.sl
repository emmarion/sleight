; error: `settled-val-apply` takes this handle at `(MMany)`, and its `Mult` is `(MErased)`
; needs: ../std/macro
(let ((many k)) 3)
(let ((many s)) "x")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) _here) (many (List $ Raw) _args) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many _)) (settled-val-apply mw (settled-of many MkPair) (settled-of erased nat-type) (settled-of erased nat-type) (settled-of erased k) (settled-of many k)))
  (values mw1 (Nil _)))
