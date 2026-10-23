; needs: ../std/macro macro_lib
; error: a handle to 3, made `erased`, used in a non-erased position
(let ((many k)) 3)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((erased e)) k)
  (values mw $ Cons _ (RawSettled here _ _ _ (settled-of erased e)) $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(let ((erased fine)) (m))
(m)
