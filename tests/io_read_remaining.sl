; stdin: first
; stdin: second
; stdin: third
; expect: line: first
; expect: rest: second
; expect: third
; ReadRemaining takes what ReadLine has not consumed, as a channel's position would.

(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some _ s) ((None _) (values w1 (Exit P code0))))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append "line: " (str-append s "\n")))))
  (let ((unique w3) (many rest)) (world-do _ w2 (ReadRemaining)))
  (let ((unique w4) (many _)) (world-do _ w3 (WriteOut (str-append "rest: " (str-append rest "\n")))))
  (values w4 (Exit P code0)))

(Continue P start)
