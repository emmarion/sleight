(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (attempt w1 (pick (arg-nat args 1 0)) program (arg-nat args 0 1)))

(Continue P start)
