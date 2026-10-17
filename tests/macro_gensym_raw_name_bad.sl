; error: unbound name `__g1_#"a b"`
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "a b"))
  (values mw1 $ Cons _ (RawSymbol here (SGen k "a b" g)) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
