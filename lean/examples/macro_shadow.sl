(def-fns _ $ (many pass : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many splice)) (MkMacro _ pass))
(def-fns _ $ (many splice : (subterm many (Nat) n) -> (many (Nat) m))
  (match many n _ ((Zero) 0) ((Succ k) (splice k))))
(splice 3)
