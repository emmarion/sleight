; stdin: a
; expect: > a
; exit: 3
; The warning is given after a `Program` has run, and one that does not depend on the `sorry` runs to its exit.
(def-lvl PA)
(def-lvl P)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes _ _ _ _ zp3))
(let ((many code3)) (MkU8 3 zp3))
(def-fns PA $ (many echo : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some _ s) ((None _) (values w1 (Exit P code3))))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut (str-append "> " (str-append s "\n")))))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p)) (echo v))
  (values w3 (Continue P again)))
(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p)) (echo w))
(let ((erased _q)) (sorry (((Lt 1 2) q))))
(Continue P start)
; warns: tests/sorry_program.sl:17:20: warning: this unit uses `sorry` once, here; nothing that depends on it runs
