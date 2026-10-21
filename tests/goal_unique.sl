; goal: proved
(let ((many aim)) goal)
(aim unique (List (Nat)))
(qed (Cons (Nat) 1 (Nil (Nat))))
; expect: --goal proved: PASS
; stderr: tests/goal_unique.sl:3:1: note: proved `(aim unique (List (Nat)))`
; stderr: tests/goal_unique.sl:4:1: note: by this `qed`
