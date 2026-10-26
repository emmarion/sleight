; error: `umac`, declared `unique`, used at many without `share`
(def-fns _ $ (many m : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((unique umac)) (MkMacro _ m))
(umac 1)
