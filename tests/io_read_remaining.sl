; stdin: first
; stdin: second
; stdin: third
; expect: line: first
; expect: rest: second
; expect: third
; ReadRemaining takes what ReadLine has not consumed, as a channel's position would.

(def-lvl P)
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (erased str-p) (prove-predates str-lvl P))
(let (erased thunk-p) (prove-predates thunk-lvl P))

(def-fns P $ many after-rest : (many (String) rest) -> (many (IO P) next)
  (WriteOut P (str-append (predates str-p) "rest: " (str-append (predates str-p) rest "\n")) (thunk (predates thunk-p) _ _ (Exit P code0))))

(def-fns P $ many after-line : (many (Maybe (String)) line) -> (many (IO P) next)
  (match many line _
    ((None a) (Exit P code0))
    ((Some a s) (WriteOut P (str-append (predates str-p) "line: " (str-append (predates str-p) s "\n")) (thunk (predates thunk-p) _ _ (ReadRemaining P after-rest))))))

(ReadLine P after-line)
