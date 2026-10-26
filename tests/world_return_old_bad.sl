; error: conflicting non-erased uses
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za zb zp))
(let ((many code0)) (MkU8 0 zp))
(def-lvl P)
(def-unique P $ (unique k : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many a)) (world-do _ w (WriteOut "a\n")))
  (values w (Exit _ code0)))
(Continue _ k)
