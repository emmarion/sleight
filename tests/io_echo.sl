; stdin: a
; stdin: bb
; expect: > a
; expect: > bb
; exit: 3
; An IO program: a ReadLine request whose continuation answers with the next request, so the driver's loop
; reads until end of input; Exit carries a U8 code. A continuation is a UniqueFn, born by def-unique and
; consumed by the request it is stored in, so the loop's body sits below the IO level and each request
; wraps it in a fresh continuation.

(def-lvl PA)
(def-lvl P)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes za3 zb3 zp3))
(let ((many code3)) (MkU8 3 zp3))
(let ((erased str-pa)) (prove-predates str-lvl PA))
(let ((erased thunk-pa)) (prove-predates thunk-lvl PA))
(let ((erased pa-p)) (prove-predates PA P))

(def-fns PA $ (many echo : (many (Maybe (String)) line) -> (unique (IO P) next))
  (match many line _
    ((None a) (Exit P code3))
    ((Some a s)
      (def-unique P $ (unique again : (many (Maybe (String)) next-line) -> (unique (IO P) next)) (echo (predates pa-p) line))
      (WriteOut P (str-append (predates str-pa) "> " (str-append (predates str-pa) s "\n"))
        (unique-thunk (predates thunk-pa) _ _ (ReadLine P again))))))

(def-unique P $ (unique start : (many (Maybe (String)) line) -> (unique (IO P) next)) (echo (predates pa-p) line))

(ReadLine P start)
