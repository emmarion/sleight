; stdin: a
; stdin: bb
; expect: > a
; expect: > bb
; exit: 3
; An IO program: a ReadLine request whose continuation answers with the next request, holding itself,
; so the driver's loop reads until end of input; Exit carries a U8 code.

(def-lvl P)
(let (erased u8-p) (prove-predates u8-lvl P))
(let (erased str-p) (prove-predates str-lvl P))

(def-fns P $ many echo : (many (Maybe (String)) line) -> (many (IO P) next)
  (match many line _
    ((None a) (Exit P (nat-to-u8 (predates u8-p) 3)))
    ((Some a s) (WriteOut P (str-append (predates str-p) "> " (str-append (predates str-p) s "\n")) (ReadLine P echo)))))

(ReadLine P echo)
