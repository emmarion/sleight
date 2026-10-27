; expect: made
; expect: again
; expect: a.txt
; expect: b.txt
; expect: not empty
; expect: absent
; expect: cleaned
; expect: missing directory refused
; MkDir reports Changed the first time and Unchanged the second; DeleteDir refuses a directory that still
; holds entries and reports Unchanged for one that was never there; DeleteFile reports Unchanged for an
; absent file and is refused inside a directory that is gone; ListDir sorts and drops "." and "..".
; A failure ends the program through a Result-returning step, its helpers threading the world.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes _ _ za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-fns _ $ (many say : (many (String) text) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut text)))
  w1)

(def-fns _ $ (many changed : (many (String) yes) (many (String) no) (unique (World) w at vacant-slot) (unique (Request (Result (Change))) req) ->
    (unique (World) w2 at w) (many (Bool) ok))
  (let ((unique w1) (many o)) (world-do _ w req))
  (let-match many o (Ok _ c) ((Fail _ m) (let ((unique w2) (many _)) (world-do _ w1 (WriteErr m))) (values w2 (BFalse))))
  (match many c (((World) w2 at w) ((Bool) ok))
    ((Changed) (values (say yes w1) (BTrue)))
    ((Unchanged) (values (say no w1) (BFalse)))))

(def-fns _ $ (many show-entries : (subterm many (List (String)) es) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let-match many es (Cons _ e rest) ((Nil _) w))
  (tail $ show-entries rest (say (str-append e "\n") w)))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many _)) (world-do _ w (DeleteFile "io-dir-test/a.txt")))
  (let ((unique w2) (many _)) (world-do _ w1 (DeleteFile "io-dir-test/b.txt")))
  (let ((unique w3) (many _)) (world-do _ w2 (DeleteDir "io-dir-test")))
  (let ((unique w4) (many ok4)) (changed "made\n" "already there\n" w3 (MkDir "io-dir-test")))
  (let-match many ok4 (BTrue) ((BFalse) (values w4 (Exit P code1))))
  (let ((unique w5) (many ok5)) (changed "made twice\n" "again\n" w4 (MkDir "io-dir-test")))
  (let-match many ok5 (BFalse) ((BTrue) (values w5 (Exit P code1))))
  (let ((unique w6) (many _)) (world-do _ w5 (WriteFile "io-dir-test/b.txt" "")))
  (let ((unique w7) (many _)) (world-do _ w6 (WriteFile "io-dir-test/a.txt" "")))
  (let ((unique w8) (many listed)) (world-do _ w7 (ListDir "io-dir-test")))
  (let-match many listed (Ok _ es) ((Fail _ m) (values (say m w8) (Exit P code1))))
  (let ((unique w9)) (show-entries es w8))
  (let ((unique w10) (many full)) (world-do _ w9 (DeleteDir "io-dir-test")))
  (let-match many full (Fail _ _) ((Ok _ _) (values (say "removed a full directory\n" w10) (Exit P code1))))
  (let ((unique w11)) (say "not empty\n" w10))
  (let ((unique w12) (many _)) (world-do _ w11 (DeleteFile "io-dir-test/a.txt")))
  (let ((unique w13) (many ok13)) (changed "deleted twice\n" "absent\n" w12 (DeleteFile "io-dir-test/a.txt")))
  (let-match many ok13 (BFalse) ((BTrue) (values w13 (Exit P code1))))
  (let ((unique w14) (many _)) (world-do _ w13 (DeleteFile "io-dir-test/b.txt")))
  (let ((unique w15) (many ok15)) (changed "cleaned\n" "never made\n" w14 (DeleteDir "io-dir-test")))
  (let-match many ok15 (BTrue) ((BFalse) (values w15 (Exit P code1))))
  (let ((unique w16) (many gone)) (world-do _ w15 (DeleteFile "io-dir-test/a.txt")))
  (let-match many gone (Fail _ _) ((Ok _ _) (values (say "deleted in a missing directory\n" w16) (Exit P code1))))
  (let ((unique w17)) (say "missing directory refused\n" w16))
  (values w17 (Exit P code0)))

(Continue P start)
