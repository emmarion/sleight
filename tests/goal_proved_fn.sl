; needs: goal_spec
; goal: proved
(def-fns _ $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (let ((many m) (erased _)) (add n n))
  m)
(MkDoubler (level-of twice) twice)
; stderr: tests/goal_spec.sl:6:1: note: proved `(goal many (Doubler))`
