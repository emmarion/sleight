; stdin: a
; stdin: bb
; expect: > a
; expect: > bb
; exit: 3
; A Program reading until end of input: each step's continuation is a UniqueFn that takes the world at unique
; and gives it back at itself, performing its requests with world-do in between, and returns the next step;
; Exit carries a U8 code. The loop's body sits below the program's level, and each step wraps it in a fresh
; continuation, so the driver's loop is what iterates.

(def-lvl PA)
(def-lvl P)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes za3 zb3 zp3))
(let ((many code3)) (MkU8 3 zp3))

(def-fns PA $ (many echo : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some a s) ((None a) (values w1 (Exit P code3))))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut (str-append "> " (str-append s "\n")))))
  (def-unique P $ (unique again : (unique (World) v) -> (unique (World) v2 at v) (unique (Program P) p)) (echo v))
  (values w3 (Continue P again)))

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p)) (echo w))

(Continue P start)
