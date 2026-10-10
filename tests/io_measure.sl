; expect: 5050
; Measure answers the program's usage since its first step; under --no-extern every figure is zero, so the
; test prints the work's result, not the figures.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za zb zp))

(def-fns _ $ (many sum-to : (subterm many (Nat) n) -> (many (Nat) s))
  (let-match many n (Succ m) ((Zero) 0))
  (nat-add n (notail $ sum-to m)))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((many s)) (sum-to 100))
  (let ((unique w1) (many u)) (world-do _ w (Measure (Compact))))
  (let ((unique w2) (many u2)) (world-do _ w1 (Measure (NoCompact))))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut (str-append (nat-str s) "\n"))))
  (values w3 (Exit P (MkU8 0 zp))))

(Continue P start)
