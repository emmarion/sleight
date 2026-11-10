; goal: proved
; A `sorry` fails `--goal proved`, though the `qed` does not depend on it, even one in erased code that never runs.
(def-fns _ $ (erased lemma : (many (Nat) _n) -> (erased (Lt 1 2) p))
  (sorry _))
(let ((many _m)) (sorry (((Nat) x))))
(goal many (Nat))
(qed 3)
; error: tests/sorry_goal_proved_bad.sl:4:3: error: under `--goal proved` a unit may not use `sorry`, and this one uses it 2 times, first here
