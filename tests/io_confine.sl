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
; expect: stat absent ok
; expect: stat through absent refused
; expect: stat past absent refused
; expect: stat parent refused
; expect: list cwd refused
; expect: write outside refused
; expect: confine file refused
; expect: delete file ok
; expect: delete fence refused
; expect: mkdir fence refused
; expect: drop writes ok
; expect: write after drop refused
; expect: stat after drop ok
; expect: confine nothing ok
; expect: stat after nothing refused
; A program confines itself to a directory it reads and one it writes: a path the confinement admits behaves
; as it would unconfined, one it does not is refused whether it names something or not, the confinement
; only narrows, and an entry is created or removed only inside a writable directory, so not the writable
; directory itself. What the test made under its read-only directory stays, and the next run reuses it.

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
  (let ((unique w5)) (report _ "confine" w4 (Confine (one "io-confine-test/r") (one "io-confine-test/w"))))
  (let ((unique w6)) (report _ "widen write" w5 (Confine (Nil _) (one "io-confine-test/r"))))
  (let ((unique w7)) (report _ "widen read" w6 (Confine (one ".") (one "io-confine-test/w"))))
  (let ((unique w8)) (report _ "same fence" w7 (Confine (Cons _ "io-confine-test/r/." $ one "io-confine-test/w") (one "io-confine-test/w/../w"))))
  (let ((unique w9)) (report _ "read r" w8 (ReadFile "io-confine-test/r/a.txt")))
  (let ((unique w10)) (report _ "list r" w9 (ListDir "io-confine-test/r")))
  (let ((unique w11)) (report _ "write into r" w10 (WriteFile "io-confine-test/r/b.txt" "x")))
  (let ((unique w12)) (report _ "mkdir into r" w11 (MkDir "io-confine-test/r/d")))
  (let ((unique w13)) (report _ "delete from r" w12 (DeleteFile "io-confine-test/r/a.txt")))
  (let ((unique w14)) (report _ "write w" w13 (WriteFile "io-confine-test/w/c.txt" "hi")))
  (let ((unique w15)) (report _ "read w" w14 (ReadFile "io-confine-test/w/c.txt")))
  (let ((unique w16)) (report _ "mkdir in w" w15 (MkDir "io-confine-test/w/in")))
  (let ((unique w17)) (report _ "delete in w" w16 (DeleteDir "io-confine-test/w/in")))
  (let ((unique w18)) (report _ "stat absent" w17 (Stat "io-confine-test/w/nope")))
  (let ((unique w19)) (report _ "stat through absent" w18 (Stat "io-confine-test/w/nope/..")))
  (let ((unique w20)) (report _ "stat past absent" w19 (Stat "io-confine-test/w/nope/../in")))
  (let ((unique w21)) (report _ "stat parent" w20 (Stat "io-confine-test")))
  (let ((unique w22)) (report _ "list cwd" w21 (ListDir ".")))
  (let ((unique w23)) (report _ "write outside" w22 (WriteFile "io-confine-test/w/../../io-confine-escape.txt" "x")))
  (let ((unique w24)) (report _ "confine file" w23 (Confine (Nil _) (one "io-confine-test/w/c.txt"))))
  (let ((unique w25)) (report _ "delete file" w24 (DeleteFile "io-confine-test/w/c.txt")))
  (let ((unique w26)) (report _ "delete fence" w25 (DeleteDir "io-confine-test/w")))
  (let ((unique w27)) (report _ "mkdir fence" w26 (MkDir "io-confine-test/w")))
  (let ((unique w28)) (report _ "drop writes" w27 (Confine (Cons _ "io-confine-test/r" $ one "io-confine-test/w") (Nil _))))
  (let ((unique w29)) (report _ "write after drop" w28 (WriteFile "io-confine-test/w/c.txt" "x")))
  (let ((unique w30)) (report _ "stat after drop" w29 (Stat "io-confine-test/w")))
  (let ((unique w31)) (report _ "confine nothing" w30 (Confine (Nil _) (Nil _))))
  (let ((unique w32)) (report _ "stat after nothing" w31 (Stat "io-confine-test/w")))
  (values w32 (Exit P code0)))

(Continue P start)
