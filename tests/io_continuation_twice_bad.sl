; error: conflicting non-erased uses
; A continuation is consumed by the request that holds it, so one cannot serve two requests.

(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(def-unique P $ (unique k : -> (unique (IO P) next)) (Exit P code0))
(let ((unique first)) (Step P k))
(Step P k)
