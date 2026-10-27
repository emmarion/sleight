; confine-output-bytes: 10000
; expect: mkdir ok
; expect: write new ok
; expect: rewrite ok
; expect: raise refused
; expect: lower ok
; expect: delete file ok
; expect: delete dir ok
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 12383 bytes, over its limit of 9000
; exit: 1

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w at vacant-slot) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  w2)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "mkdir" w (MkDir "io-output-limit-test")))
  (let ((unique w2)) (report _ "write new" w1 (WriteFile "io-output-limit-test/a.txt" "hello")))
  (let ((unique w3)) (report _ "rewrite" w2 (WriteFile "io-output-limit-test/a.txt" "hello")))
  (let ((unique w4)) (report _ "raise" w3 (ConfineOutputBytes 20000)))
  (let ((unique w5)) (report _ "lower" w4 (ConfineOutputBytes 9000)))
  (let ((unique w6)) (report _ "delete file" w5 (DeleteFile "io-output-limit-test/a.txt")))
  (let ((unique w7)) (report _ "delete dir" w6 (DeleteDir "io-output-limit-test")))
  (let ((unique w8) (many _)) (world-do _ w7 (MkDir "io-output-limit-test")))
  (values w8 (Exit P code0)))

(Continue P start)
