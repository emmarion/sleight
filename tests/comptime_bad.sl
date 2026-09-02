; needs: list
; error: expected Zero, got (Succ (Succ (Zero)))

(let (many two) (Succ (Succ (Zero))))
(comptime-match two (Zero))
