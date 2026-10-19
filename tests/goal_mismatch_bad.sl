; goal: proved
(goal erased (False))
(def-adts ((False : -> Type) enum (many Boom : -> (False))))
(Boom)
; error: type mismatch: expected `(__1)`, got `(False)`
; warns: tests/goal_mismatch_bad.sl:3:12: warning: declaration of `False` shadows a previous binder
; warns: lib/prelude.sl:15:13: note: shadowed binder is here
