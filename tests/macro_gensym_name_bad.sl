; error: unbound name `__g1_tmp`
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "tmp"))
  (values mw1 $ Cons _ (RawSymbol here (SGen k "tmp" g)) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
