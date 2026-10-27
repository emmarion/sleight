; expect: Hello, world!
; exit: 0
(def-lvl P)
(let ((many d)) (lt-dec 0 u8-modulus))
(comptime-match many d (Yes _ _ _ _ p))
(let ((many ok)) (MkU8 0 p))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program P) next))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut "Hello, world!\n")))
  (values w1 (Exit P ok)))

(Continue P start)
