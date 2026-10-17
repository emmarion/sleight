; confine-dir: .
; expect: stat cwd ok
; expect: list parent refused
; expect: confine cwd ok
; expect: confine parent refused
; expect: read outside refused
; The driver starts confined to the directory the command line names, here the one the program runs in.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  w2)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "stat cwd" w (Stat ".")))
  (let ((unique w2)) (report _ "list parent" w1 (ListDir "..")))
  (let ((unique w3)) (report _ "confine cwd" w2 (ConfineDir ".")))
  (let ((unique w4)) (report _ "confine parent" w3 (ConfineDir "..")))
  (let ((unique w5)) (report _ "read outside" w4 (ReadFile "../io-confine-flag.txt")))
  (values w5 (Exit P code0)))

(Continue P start)
