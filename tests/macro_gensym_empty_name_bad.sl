; error: unbound name `__g1_#""`
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw ""))
  (values mw1 $ Cons _ (RawGen here k "" g) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
