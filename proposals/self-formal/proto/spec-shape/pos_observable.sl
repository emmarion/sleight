(let ((erased PosT)) (Pos))
(def-fns _ $ (many here-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ (settled-of erased PosT) here))
  (values mw1 $ Cons _ (RawSettled here _ _ _ h) $ Nil _))
(let ((many here)) (MkMacro _ here-fn))
(MkPair _ _ (here) 	(here))
