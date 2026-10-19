; confine-read: .
; expect: stat cwd ok
; expect: list cwd ok
; expect: mkdir refused
; expect: write refused
; expect: append refused
; expect: delete refused
; expect: confine write refused
; With only a directory to read on the command line, the program writes nowhere.

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
  (let ((unique w2)) (report _ "list cwd" w1 (ListDir ".")))
  (let ((unique w3)) (report _ "mkdir" w2 (MkDir "io-confine-read-only-test")))
  (let ((unique w4)) (report _ "write" w3 (WriteFile "io-confine-read-only.txt" "x")))
  (let ((unique w5)) (report _ "append" w4 (AppendFile "io-confine-read-only.txt" "x")))
  (let ((unique w6)) (report _ "delete" w5 (DeleteFile "io-confine-read-only.txt")))
  (let ((unique w7)) (report _ "confine write" w6 (ConfinePaths (Nil _) (Cons _ "." $ Nil _))))
  (values w7 (Exit P code0)))

(Continue P start)
