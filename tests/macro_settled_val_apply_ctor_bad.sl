; error: `settled-val-apply` takes a handle to a value constructor first, and `Lt` has type
(let ((many k)) 3)
(let ((many s)) "x")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) _here) (many (List $ Raw) _args) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many _)) (settled-val-apply mw (settled-of erased Lt) (settled-of erased k) (settled-of erased k)))
  (values mw1 (Nil _)))
