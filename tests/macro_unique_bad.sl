; error: `umac`, declared `unique`, used at many without `share`
(def-fns _ $ (many m : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  args)
(let ((unique umac)) (MkMacro _ m))
(umac 1)
