; expect: tick
; expect: tick
; expect: done
; A continuation that performs nothing hands the next step straight back to the driver, so a program can
; iterate without an effect, and a loop can as well be written with output alone. Both loops defer to the
; driver rather than recursing: the continuation is a level-P closure over the decremented count, and P
; comes after the loop's own level, so neither function can call it. The unbounded iteration is the
; driver's, as it is for a ReadLine loop.

(def-lvl P1)
(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns P1 $ (many shout : (subterm many (Nat) n) (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) next))
  (let-match many n (Succ m) ((Zero) (let ((unique w1) (many _)) (world-do _ w (WriteOut "done\n"))) (values w1 (Exit P code0))))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut "tick\n")))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) next))
    (shout m v))
  (values w1 (Continue P again)))

(def-fns PA $ (many settle : (subterm many (Nat) n) -> (unique (Program P) next))
  (let-match many n (Succ m)
    ((Zero)
      (def-unique P $ (unique go : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) next)) (shout 2 v))
      (Continue P go)))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) next))
    (values v (settle m)))
  (Continue P again))

(settle 3)
