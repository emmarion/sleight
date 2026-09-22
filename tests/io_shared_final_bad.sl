; error: used at unique
; The driver consumes an IO value at unique, so a shared one cannot be a program: its continuations are
; UniqueFns a share has left callable only erased.

(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((unique prog)) (Exit P code0))
(share prog)
