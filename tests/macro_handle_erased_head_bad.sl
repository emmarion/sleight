; needs: ../std/macro macro_lib
; error: made `erased`, used in a non-erased position
; warns: <**>:6:9: warning: `h` is referenced only in erased positions; declare it `erased`
(def-fns _ $ (many plus-k-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many h)) nat-add)
  (values mw $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of erased h)) args) $ Nil _))
(let ((many plus-k)) (MkMacro _ plus-k-fn))
(plus-k 1 2)
