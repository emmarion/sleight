; expect: once
; exit: 3
(def-lvl P)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes za3 zb3 zp3))
(let ((many code3)) (MkU8 3 zp3))
(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((erased w1) (erased u)) (world-do _ w (WriteOut "never\n")))
  (let ((unique w3) (many _)) (world-do _ w (WriteOut "once\n")))
  (values w3 (Exit P code3)))
(Continue P start)
