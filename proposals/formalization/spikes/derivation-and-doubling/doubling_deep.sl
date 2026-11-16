(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many n)) (arg-nat args 0 3000))
  (let ((many k)) (arg-nat args 2 0))
  (attempt w1 (pick (arg-nat args 3 0)) (match many k _ ((Zero) (deep-program n)) ((Succ _) (wide-program k n))) (arg-nat args 1 1)))

(Continue P start)
