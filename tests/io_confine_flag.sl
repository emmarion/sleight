; confine-read: ..
; confine-write: io-confine-flag-test
; expect: stat cwd ok
; expect: list parent ok
; expect: list grandparent refused
; expect: write cwd refused
; expect: mkdir ok
; expect: write in ok
; expect: delete in ok
; expect: delete ok
; expect: confine same ok
; expect: confine cwd refused
; expect: read outside refused
; The driver starts confined as the command line says, here reading the directory above the one the program
; runs in and writing one path that does not exist yet.

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
  (let ((unique w3)) (report _ "list grandparent" w2 (ListDir "../..")))
  (let ((unique w4)) (report _ "write cwd" w3 (WriteFile "io-confine-flag.txt" "x")))
  (let ((unique w5)) (report _ "mkdir" w4 (MkDir "io-confine-flag-test")))
  (let ((unique w6)) (report _ "write in" w5 (WriteFile "io-confine-flag-test/a.txt" "x")))
  (let ((unique w7)) (report _ "delete in" w6 (DeleteFile "io-confine-flag-test/a.txt")))
  (let ((unique w8)) (report _ "delete" w7 (DeleteDir "io-confine-flag-test")))
  (let ((unique w9)) (report _ "confine same" w8 (ConfinePaths (Cons _ ".." $ Nil _) (Cons _ "io-confine-flag-test" $ Nil _))))
  (let ((unique w10)) (report _ "confine cwd" w9 (ConfinePaths (Nil _) (Cons _ "." $ Nil _))))
  (let ((unique w11)) (report _ "read outside" w10 (ReadFile "../../io-confine-flag.txt")))
  (values w11 (Exit P code0)))

(Continue P start)
