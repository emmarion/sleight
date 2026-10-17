; expect: onetwo
; expect: file
; expect: missing
; expect: cwd: dir
; AppendFile adds to what WriteFile left; Stat names what a path holds, Missing being an ordinary answer.
; GetCwd's value is the machine's, so the test asks Stat what it names rather than printing it.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-fns _ $ (many kind-name : (many (EntryKind) k) -> (many (String) s))
  (match many k _
    ((IsFile) "file")
    ((IsDir) "dir")
    ((IsOther) "other")
    ((Missing) "missing")))

(def-fns _ $ (many show-kind : (many (String) label) (many (Result (EntryKind)) r) (unique (World) w) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w $ match many r (((Request (Unit)) _))
    ((Ok _ k) (WriteOut (str-append label (str-append (kind-name k) "\n"))))
    ((Fail _ m) (WriteErr m))))
  w1)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many _)) (world-do _ w (DeleteFile "io-stat-test.txt")))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteFile "io-stat-test.txt" "one")))
  (let ((unique w3) (many _)) (world-do _ w2 (AppendFile "io-stat-test.txt" "two")))
  (let ((unique w4) (many read)) (world-do _ w3 (ReadFile "io-stat-test.txt")))
  (let-match many read (Ok _ s) ((Fail _ m) (let ((unique w5) (many _)) (world-do _ w4 (WriteErr m))) (values w5 (Exit P code1))))
  (let ((unique w5) (many _)) (world-do _ w4 (WriteOut (str-append s "\n"))))
  (let ((unique w6) (many file)) (world-do _ w5 (Stat "io-stat-test.txt")))
  (let ((unique w7) (many none)) (world-do _ (show-kind "" file w6) (Stat "io-stat-test-none")))
  (let ((unique w8) (many cwd)) (world-do _ (show-kind "" none w7) (GetCwd)))
  (let ((unique w9) (many here)) (world-do _ w8 (Stat cwd)))
  (let ((unique w10) (many _)) (world-do _ (show-kind "cwd: " here w9) (DeleteFile "io-stat-test.txt")))
  (values w10 (Exit P code0)))

(Continue P start)
