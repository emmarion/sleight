; no-exec: yes
; expect: Fail /bin/sh: exec is disabled (--no-exec)
; Under --no-exec every Exec request answers Fail without running anything.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many r)) (world-do _ w (Exec "/bin/sh" (Cons _ "-c" $ Cons _ "true" $ Nil _) (Nil _) (None _) "")))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut $ match many r (((String) _)) ((Ok _ _) "ran\n") ((Fail _ m) (str-append "Fail " $ str-append m "\n")))))
  (values w2 (Exit P code0)))

(Continue P start)
