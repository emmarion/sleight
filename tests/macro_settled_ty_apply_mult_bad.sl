; error: `settled-ty-apply` takes this handle at `(MErased)`, and its `Mult` is `(MMany)`
(let ((many k)) 3)
(let ((many s)) "x")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many _)) (settled-ty-apply mw (settled-of erased Lt) (settled-of many k) (settled-of erased k)))
  (values mw1 (Nil _)))
