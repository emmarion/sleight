; expect: 3
(let ((many three)) (Succ (Succ (Succ (Zero)))))
(comptime-match many (lt-dec three u8-modulus) (Yes a b p))
(let ((many x)) (MkU8 three p))
(let-match many x (MkU8 xn xq))
(coerce x (coercible-sym (coercible-wrap (Shared) MkU8 xn xq)))
