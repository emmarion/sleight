; expect: mkdir ok
; expect: mkdir in ok
; expect: write ok
; expect: write outer ok
; expect: inside read inner
; expect: back in read inner
; expect: up: ../b.txt: outside the directory io-rfi-test/in
; expect: missing: c.txt: No such file or directory
; expect: delete outer ok
; expect: confine ok
; expect: fenced refused
; expect: delete ok
; expect: delete in ok
; expect: delete fence ok
; A ReadFileIn reads a path relative to a directory and refuses one that resolves outside it, and it is
; still subject to the program's own confinement.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w at vacant-slot) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  w2)

(def-fns _ $ (many read-in : (many (String) label) (unique (World) w at vacant-slot) (many (String) dir) (many (String) path) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w (ReadFileIn dir path)))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ x) (str-append " read " $ str-append x "\n")) ((Fail _ m) (str-append ": " $ str-append m "\n"))))))
  w2)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "mkdir" w (MkDir "io-rfi-test")))
  (let ((unique w2)) (report _ "mkdir in" w1 (MkDir "io-rfi-test/in")))
  (let ((unique w3)) (report _ "write" w2 (WriteFile "io-rfi-test/in/a.txt" "inner")))
  (let ((unique w4)) (report _ "write outer" w3 (WriteFile "io-rfi-test/b.txt" "outer")))
  (let ((unique w5)) (read-in "inside" w4 "io-rfi-test/in" "a.txt"))
  (let ((unique w6)) (read-in "back in" w5 "io-rfi-test/in" "../in/a.txt"))
  (let ((unique w7)) (read-in "up" w6 "io-rfi-test/in" "../b.txt"))
  (let ((unique w8)) (read-in "missing" w7 "io-rfi-test/in" "c.txt"))
  (let ((unique w9)) (report _ "delete outer" w8 (DeleteFile "io-rfi-test/b.txt")))
  (let ((unique w10)) (report _ "confine" w9 (ConfinePaths (Nil _) (Cons _ "io-rfi-test" $ Nil _))))
  (let ((unique w11)) (report _ "fenced" w10 (ReadFileIn "." "io-rfi-elsewhere.txt")))
  (let ((unique w12)) (report _ "delete" w11 (DeleteFile "io-rfi-test/in/a.txt")))
  (let ((unique w13)) (report _ "delete in" w12 (DeleteDir "io-rfi-test/in")))
  (let ((unique w14)) (report _ "delete fence" w13 (DeleteDir "io-rfi-test")))
  (values w14 (Exit P code0)))

(Continue P start)
