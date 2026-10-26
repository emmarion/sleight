(def-fns _ $ (many pass : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many splice)) (MkMacro _ pass))
(let ((many n)) (splice (goal many (Nat))) 3)
; error: tests/goal_nested_bad.sl:5:25: error: `goal` is allowed only as a top-level form of a file
