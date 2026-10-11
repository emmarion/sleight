; error: argument 1, `mw`, of `m-fn`: `_` stands only for an erased argument
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many out)) (m-fn _ (NoPos) (Nil _)))
