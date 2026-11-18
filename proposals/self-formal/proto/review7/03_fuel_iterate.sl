(def-lvl P1)
(def-lvl P)
(def-lvl Q)
(def-lvl T)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns P1 $ (many count : (subterm many (Nat) n) -> (unique (Program P) next))
  (let-match many n (Succ m) ((Zero) (Exit P code0)))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) next))
    (values v (count m)))
  (Continue P again))

(def-fns Q $ (many run-n : (subterm many (Nat) f) (unique (Program P) p) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program P) rest))
  (let-match many f (Succ g) ((Zero) (values w p)))
  (let-match unique p (Continue _ k) ((Exit _ c) (values w (Exit P c))))
  (let ((unique w1) (unique p2)) (k w))
  (tail $ run-n g p2 w1))

(def-fns Q $ (many report : (unique (Program P) rest) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (match unique rest _
    ((Exit _ c) (let ((unique w1) (many _)) (world-do _ w (WriteOut "finished\n"))) w1)
    ((Continue _ k) (let ((unique w1) (many _)) (world-do _ w (WriteOut "out of fuel\n"))) w1)))

(def-unique T $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program T) next))
  (let ((unique w1) (unique r1)) (run-n 3 (count 5) w))
  (let ((unique w2)) (report r1 w1))
  (let ((unique w3) (unique r2)) (run-n 10 (count 5) w2))
  (let ((unique w4)) (report r2 w3))
  (values w4 (Exit T code0)))

(Continue T start)
