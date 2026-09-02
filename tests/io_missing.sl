; stderr: missing
; exit: 1
; A failed ReadFile answers its continuation with Fail.

(def-lvl P)
(let (erased u8-p) (prove-predates u8-lvl P))

(def-fns P $ many after-read : (many (Result (String)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a s) (WriteOut P s (Exit P (nat-to-u8 (predates u8-p) 0))))
    ((Fail a m) (WriteErr P "missing\n" (Exit P (nat-to-u8 (predates u8-p) 1))))))

(ReadFile P "no-such-file" after-read)
