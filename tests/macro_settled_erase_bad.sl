; needs: ../std/macro macro_lib
; error: a handle to 5, made `erased`, used in a non-erased position
(let ((many k)) 5)
(def-fns _ $ (many use-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ (settled-erase _ _ _ (settled-of many k))) $ Nil _))
(let ((many use)) (MkMacro _ use-fn))
(let ((many n)) (use))
