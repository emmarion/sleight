; error: argument 2, `b`, of `Lt`: type mismatch: expected `(Nat)`, got `(String)`
(let ((many k)) 3)
(let ((many s)) "x")
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) _here) (many (List $ Raw) _args) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many _)) (settled-ty-apply mw (settled-of erased Lt) (settled-of erased k) (settled-of erased s)))
  (values mw1 (Nil _)))
