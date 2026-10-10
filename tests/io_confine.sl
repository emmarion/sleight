; expect: mkdir ok
; expect: confine ok
; expect: widen refused
; expect: mkdir in ok
; expect: same fence ok
; expect: write ok
; expect: read ok
; expect: stat absent ok
; expect: stat parent refused
; expect: list cwd refused
; expect: write outside refused
; expect: confine file refused
; expect: delete file ok
; expect: delete in ok
; expect: delete fence ok
; A program confines itself to a directory it made: a path the fence admits behaves as it would unconfined,
; one it does not is refused whether it names something or not, the fence only narrows, and the fence's own
; directory is inside it, so the test removes all it made.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok a x) " ok\n") ((Fail a m) " refused\n")))))
  w2)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "mkdir" w (MkDir "io-confine-test")))
  (let ((unique w2)) (report _ "confine" w1 (ConfineDir "io-confine-test")))
  (let ((unique w3)) (report _ "widen" w2 (ConfineDir ".")))
  (let ((unique w4)) (report _ "mkdir in" w3 (MkDir "io-confine-test/in")))
  (let ((unique w5)) (report _ "same fence" w4 (ConfineDir "io-confine-test/in/..")))
  (let ((unique w6)) (report _ "write" w5 (WriteFile "io-confine-test/in/a.txt" "hi")))
  (let ((unique w7)) (report _ "read" w6 (ReadFile "io-confine-test/in/../in/a.txt")))
  (let ((unique w8)) (report _ "stat absent" w7 (Stat "io-confine-test/nope")))
  (let ((unique w9)) (report _ "stat parent" w8 (Stat "io-confine-test/..")))
  (let ((unique w10)) (report _ "list cwd" w9 (ListDir ".")))
  (let ((unique w11)) (report _ "write outside" w10 (WriteFile "io-confine-test/../io-confine-escape.txt" "x")))
  (let ((unique w12)) (report _ "confine file" w11 (ConfineDir "io-confine-test/in/a.txt")))
  (let ((unique w13)) (report _ "delete file" w12 (DeleteFile "io-confine-test/in/a.txt")))
  (let ((unique w14)) (report _ "delete in" w13 (DeleteDir "io-confine-test/in")))
  (let ((unique w15)) (report _ "delete fence" w14 (DeleteDir "io-confine-test")))
  (values w15 (Exit P code0)))

(Continue P start)
