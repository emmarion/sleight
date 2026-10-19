; needs: goal_spec
; goal: proved
(def-fns _ $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (let ((many m) (erased _)) (add n n))
  m)
(qed (MkDoubler (level-of twice) twice))
; stderr: tests/goal_spec.sl:6:1: note: proved `(goal many (Doubler))`
; stderr: tests/goal_proved_fn.sl:6:1: note: by this `qed`
