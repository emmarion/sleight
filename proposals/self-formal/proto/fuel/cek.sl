; With machine.sl first. args: n [batch]. Runs (sum n), written with the Z combinator, at runtime.

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many n) (many args2)) (arg-nat args 100))
  (let ((many batch) (many _)) (arg-nat args2 1))
  (drive (Running $ Eval (sum-to n) (Nil _) (Nil _)) batch 0 0 w1))

(Continue P start)
