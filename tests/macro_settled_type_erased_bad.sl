; needs: ../std/macro macro_lib
; error: a handle to `(List (Nat))`, made `erased`, used in a non-erased position
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many type-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ (settled-type _ _ _ (settled-of many xs))) $ Nil _))
(let ((many type-of-xs)) (MkMacro _ type-fn))
(let ((many t)) (type-of-xs))
