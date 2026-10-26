(def-fns _ $ (many pass : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many splice)) (MkMacro _ pass))
(splice (goal many (Nat)))
(let ((many aim)) goal)
(aim erased (False))
; error: tests/goal_second_bad.sl:7:1: error: a unit sets at most one `aim`
; error: tests/goal_second_bad.sl:5:9: note: the goal is set here
