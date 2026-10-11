; error: `umac`, declared `unique`, used at many without `share`
(def-fns _ $ (many m : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((unique umac)) (MkMacro _ m))
(umac 1)
