; With machine.sl first. args: which n [batch]. Checks a source whose splices run (sum n) at compile time, then
; runs the checked program. which: 0 accepted, 1 an unbound variable, 2 a stuck splice, 3 a diverging splice.

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many which) (many args2)) (arg-nat args 0))
  (let ((many n) (many args3)) (arg-nat args2 100))
  (let ((many batch) (many _)) (arg-nat args3 1))
  (drive (Checking (sources which n) 0 (Nil _)) batch 0 0 w1))

(Continue P start)
