; needs: macro_lib
; error: a handle to `k`, made `erased`
(let ((many k)) 3)
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((erased e)) k)
  (values mw $ one $ RawSettled here _ _ _ (settled-of erased e)))
(let ((many m)) (MkMacro _ m-fn))
(let ((erased fine)) (m))
(m)
