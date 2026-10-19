; expect: mkdir ok
; expect: mkdir r ok
; expect: mkdir w ok
; expect: write r ok
; expect: confine ok
; expect: widen write refused
; expect: widen read refused
; expect: same fence ok
; expect: read r ok
; expect: list r ok
; expect: write into r refused
; expect: mkdir into r refused
; expect: delete from r refused
; expect: write w ok
; expect: read w ok
; expect: mkdir in w ok
; expect: delete in w ok
; expect: write file ok
; expect: read file ok
; expect: write sibling refused
; expect: list parent refused
; expect: delete file ok
; expect: recreate file ok
; expect: delete file again ok
; expect: stat absent ok
; expect: stat through absent refused
; expect: stat past absent refused
; expect: list cwd refused
; expect: write outside refused
; expect: delete file in w ok
; expect: delete w ok
; expect: recreate w ok
; expect: drop writes ok
; expect: write after drop refused
; expect: stat after drop ok
; expect: confine nothing ok
; expect: stat after nothing refused
; A program confines itself to paths it reads and paths it writes: a directory it reads, a directory it writes,
; and one file it writes that does not exist yet. A path the confinement admits behaves as it would
; unconfined, one it does not is refused whether it names something or not, a writable path may be created
; and removed itself, and the confinement only narrows. What the test made under its read-only directory
; stays, and the next run reuses it.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  w2)

(def-fns _ $ (many one : (many (String) s) -> (many (List $ String) r))
  (Cons _ s $ Nil _))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "mkdir" w (MkDir "io-confine-test")))
  (let ((unique w2)) (report _ "mkdir r" w1 (MkDir "io-confine-test/r")))
  (let ((unique w3)) (report _ "mkdir w" w2 (MkDir "io-confine-test/w")))
  (let ((unique w4)) (report _ "write r" w3 (WriteFile "io-confine-test/r/a.txt" "hi")))
  (let ((unique w5)) (report _ "confine" w4 (ConfinePaths (one "io-confine-test/r") (Cons _ "io-confine-test/w" $ one "io-confine-test/f.txt"))))
  (let ((unique w6)) (report _ "widen write" w5 (ConfinePaths (Nil _) (one "io-confine-test/r"))))
  (let ((unique w7)) (report _ "widen read" w6 (ConfinePaths (one ".") (one "io-confine-test/w"))))
  (let ((unique w8)) (report _ "same fence" w7 (ConfinePaths (Cons _ "io-confine-test/r/." $ one "io-confine-test/w") (Cons _ "io-confine-test/w/../w" $ one "io-confine-test/f.txt"))))
  (let ((unique w9)) (report _ "read r" w8 (ReadFile "io-confine-test/r/a.txt")))
  (let ((unique w10)) (report _ "list r" w9 (ListDir "io-confine-test/r")))
  (let ((unique w11)) (report _ "write into r" w10 (WriteFile "io-confine-test/r/b.txt" "x")))
  (let ((unique w12)) (report _ "mkdir into r" w11 (MkDir "io-confine-test/r/d")))
  (let ((unique w13)) (report _ "delete from r" w12 (DeleteFile "io-confine-test/r/a.txt")))
  (let ((unique w14)) (report _ "write w" w13 (WriteFile "io-confine-test/w/c.txt" "hi")))
  (let ((unique w15)) (report _ "read w" w14 (ReadFile "io-confine-test/w/c.txt")))
  (let ((unique w16)) (report _ "mkdir in w" w15 (MkDir "io-confine-test/w/in")))
  (let ((unique w17)) (report _ "delete in w" w16 (DeleteDir "io-confine-test/w/in")))
  (let ((unique w18)) (report _ "write file" w17 (WriteFile "io-confine-test/f.txt" "hi")))
  (let ((unique w19)) (report _ "read file" w18 (ReadFile "io-confine-test/f.txt")))
  (let ((unique w20)) (report _ "write sibling" w19 (WriteFile "io-confine-test/g.txt" "x")))
  (let ((unique w21)) (report _ "list parent" w20 (ListDir "io-confine-test")))
  (let ((unique w22)) (report _ "delete file" w21 (DeleteFile "io-confine-test/f.txt")))
  (let ((unique w23)) (report _ "recreate file" w22 (WriteFile "io-confine-test/f.txt" "again")))
  (let ((unique w24)) (report _ "delete file again" w23 (DeleteFile "io-confine-test/f.txt")))
  (let ((unique w25)) (report _ "stat absent" w24 (Stat "io-confine-test/w/nope")))
  (let ((unique w26)) (report _ "stat through absent" w25 (Stat "io-confine-test/w/nope/..")))
  (let ((unique w27)) (report _ "stat past absent" w26 (Stat "io-confine-test/w/nope/../c.txt")))
  (let ((unique w28)) (report _ "list cwd" w27 (ListDir ".")))
  (let ((unique w29)) (report _ "write outside" w28 (WriteFile "io-confine-test/w/../../io-confine-escape.txt" "x")))
  (let ((unique w30)) (report _ "delete file in w" w29 (DeleteFile "io-confine-test/w/c.txt")))
  (let ((unique w31)) (report _ "delete w" w30 (DeleteDir "io-confine-test/w")))
  (let ((unique w32)) (report _ "recreate w" w31 (MkDir "io-confine-test/w")))
  (let ((unique w33)) (report _ "drop writes" w32 (ConfinePaths (Cons _ "io-confine-test/r" $ one "io-confine-test/w") (Nil _))))
  (let ((unique w34)) (report _ "write after drop" w33 (WriteFile "io-confine-test/w/c.txt" "x")))
  (let ((unique w35)) (report _ "stat after drop" w34 (Stat "io-confine-test/w")))
  (let ((unique w36)) (report _ "confine nothing" w35 (ConfinePaths (Nil _) (Nil _))))
  (let ((unique w37)) (report _ "stat after nothing" w36 (Stat "io-confine-test/w")))
  (values w37 (Exit P code0)))

(Continue P start)
