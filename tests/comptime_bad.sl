; needs: list
; error: expected Zero, got 2

(let (many two) (Succ (Succ (Zero))))
(comptime-match many two (Zero))
