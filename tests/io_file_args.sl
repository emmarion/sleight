; args: x y
; expect: file contents
; stderr: x
; stderr: y
; Writes a file, reads it back to stdout, then lists the arguments on stderr. The recursive helper over the
; argument list threads the world, giving it back at itself.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(let ((many d2)) (lt-dec 2 u8-modulus))
(comptime-match many d2 (Yes za2 zb2 zp2))
(let ((many code2)) (MkU8 2 zp2))

(def-fns _ $ (many list-args : (subterm many (List (String)) args) (unique (World) w) -> (unique (World) w2 at w))
  (let-match many args (Cons a x rest) ((Nil a) w))
  (let ((unique w1) (many _)) (world-do _ w (WriteErr (str-append x "\n"))))
  (tail $ list-args rest w1))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many wrote)) (world-do _ w (WriteFile "io-test.txt" "file contents\n")))
  (let-match many wrote (Ok a u) ((Fail a m) (let ((unique w2) (many _)) (world-do _ w1 (WriteErr m))) (values w2 (Exit P code2))))
  (let ((unique w2) (many read)) (world-do _ w1 (ReadFile "io-test.txt")))
  (let-match many read (Ok b s) ((Fail b m) (let ((unique w3) (many _)) (world-do _ w2 (WriteErr m))) (values w3 (Exit P code1))))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut s)))
  (let ((unique w4) (many args)) (world-do _ w3 (GetArgs)))
  (values (list-args args w4) (Exit P code0)))

(Continue P start)
