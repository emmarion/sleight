; stderr: missing
; exit: 1
; A failed ReadFile answers its continuation with Fail.

(def-lvl P)
(let ((erased thunk-p)) (prove-predates thunk-lvl P))
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-unique P $ (unique after-read : (many (Result (String)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a s) (WriteOut P s (unique-thunk (predates thunk-p) _ _ (Exit P code0))))
    ((Fail a m) (WriteErr P "missing\n" (unique-thunk (predates thunk-p) _ _ (Exit P code1))))))

(ReadFile P "no-such-file" after-read)
; warns: tests/io_missing.sl:16:43: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_missing.sl:17:55: warning: unnecessary `(predates _)`; drop it
