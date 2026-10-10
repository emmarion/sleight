; error: does not erase to nothing
(def-fns _ $ (many at say : (unique (World) w) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut "a\n")))
  w1)
