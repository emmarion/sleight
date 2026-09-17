; stdin: a
; stdin: bb
; expect: > a
; expect: > bb
; exit: 3
; An IO program: a ReadLine request whose continuation answers with the next request, holding itself,
; so the driver's loop reads until end of input; Exit carries a U8 code.

(def-lvl P)
(let (many d3) (lt-dec 3 u8-modulus))
(comptime-match d3 (Yes za3 zb3 zp3))
(let (many code3) (MkU8 3 zp3))
(let (erased str-p) (prove-predates str-lvl P))
(let (erased thunk-p) (prove-predates thunk-lvl P))

(def-fns P $ many echo : (many (Maybe (String)) line) -> (many (IO P) next)
  (match many line _
    ((None a) (Exit P code3))
    ((Some a s)
      (WriteOut P (str-append (predates str-p) "> " (str-append (predates str-p) s "\n"))
        (thunk (predates thunk-p) _ _ (ReadLine P echo))))))

(ReadLine P echo)
