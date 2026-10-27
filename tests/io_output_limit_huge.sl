; externs: only
; expect: huge unlimited ok
; expect: lower ok
; expect: huge refused
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 53 bytes, over its limit of 50
; exit: 1

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w at vacant-slot) (unique (Request (Result A)) req) -> (unique (World) w2 at w) (many (Result A) r))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  (values w2 r))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many _)) (report _ "huge unlimited" w (ConfineOutputBytes 1180591620717411303424)))
  (let ((unique w2) (many _)) (report _ "lower" w1 (ConfineOutputBytes 50)))
  (let ((unique w3) (many r)) (report _ "huge" w2 (ConfineOutputBytes 1180591620717411303424)))
  (let ((unique w4) (many _)) (world-do _ w3 (WriteOut (str-append "this line does not fit" $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  (values w4 (Exit P code0)))

(Continue P start)
