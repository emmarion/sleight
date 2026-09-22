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
(let ((erased str-p)) (prove-predates str-lvl P))
(let ((erased thunk-p)) (prove-predates thunk-lvl P))

(def-unique P $ (unique after-rest : (many (String) rest) -> (unique (IO P) next))
  (WriteOut P (str-append (predates str-p) "rest: " (str-append (predates str-p) rest "\n")) (unique-thunk (predates thunk-p) _ _ (Exit P code0))))

(def-unique P $ (unique after-line : (many (Maybe (String)) line) -> (unique (IO P) next))
  (match many line _
    ((None a) (Exit P code0))
    ((Some a s) (WriteOut P (str-append (predates str-p) "line: " (str-append (predates str-p) s "\n")) (unique-thunk (predates thunk-p) _ _ (ReadRemaining P after-rest))))))

(ReadLine P after-line)
