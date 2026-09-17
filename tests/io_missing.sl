; stderr: missing
; exit: 1
; A failed ReadFile answers its continuation with Fail.

(def-lvl P)
(let (erased thunk-p) (prove-predates thunk-lvl P))
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (many d1) (lt-dec 1 u8-modulus))
(comptime-match d1 (Yes za1 zb1 zp1))
(let (many code1) (MkU8 1 zp1))

(def-fns P $ many after-read : (many (Result (String)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a s) (WriteOut P s (thunk (predates thunk-p) _ _ (Exit P code0))))
    ((Fail a m) (WriteErr P "missing\n" (thunk (predates thunk-p) _ _ (Exit P code1))))))

(ReadFile P "no-such-file" after-read)
