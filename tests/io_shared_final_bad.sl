; error: used at unique
; The driver consumes a Program at unique, so a shared one cannot be a program: its continuation is a
; UniqueFn a share has left callable only erased.

(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((unique prog)) (Exit P code0))
(share prog)
