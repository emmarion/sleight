(let ((many three)) (Succ (Succ (Succ (Zero)))))
(comptime-match many (lt-dec u8-modulus three) (Yes _ _ a b p))
; error: `comptime-match`: expected `Yes`, got
