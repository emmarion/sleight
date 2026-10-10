; stderr: missing
; exit: 1
; A failed ReadFile answers Fail.

(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many r)) (world-do _ w (ReadFile "no-such-file")))
  (match many r (((World) w2 at w) ((Program P) p))
    ((Ok a s) (let ((unique w2) (many _)) (world-do _ w1 (WriteOut s))) (values w2 (Exit P code0)))
    ((Fail a m) (let ((unique w2) (many _)) (world-do _ w1 (WriteErr "missing\n"))) (values w2 (Exit P code1)))))

(Continue P start)
