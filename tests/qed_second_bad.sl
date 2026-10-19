(goal many (Nat))
(qed 3)
(let ((many done)) qed)
(done 4)
; error: tests/qed_second_bad.sl:4:1: error: a unit has at most one `done`
; error: tests/qed_second_bad.sl:2:1: note: the goal is proved here
