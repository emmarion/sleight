; goal: open
; A `sorry` fails `--goal open`, though the goal does not depend on it.
(let ((erased _p)) (sorry (((Lt 1 2) q))))
(goal erased (False))
; error: tests/sorry_goal_open_bad.sl:3:20: error: under `--goal open` a unit may not use `sorry`, and this one uses it once, here
