(def-fns _ $ (many gs-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many k) (erased g)) (gensym mw "t"))
  (let ((unique mw2) (many h)) (intern-nat mw1 k))
  (values mw2 $ Cons _ (RawSettled here _ _ _ h) $ Nil _))
(let ((many gs)) (MkMacro _ gs-fn))
(MkPair _ _ (MkPair _ _ (MkPair _ _ (gs) (gs)) (gs)) (MkPair _ _ (gs) (gs)))
