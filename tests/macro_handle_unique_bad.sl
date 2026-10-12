; needs: ../std/macro macro_lib
; error: unique value `u` has conflicting non-erased uses
(let ((unique u)) (MkPair _ _ 1 2))
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawSettled here _ _ _ (settled-of unique u)))
(let ((many take)) (MkMacro _ m-fn))
(let ((unique a)) (take))
(let ((unique b)) (take))
