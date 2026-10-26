; expect: 3
; host-path: yes
; native-compute: the bound of tests/u8.sl decided by lt-dec compiled.

(let ((many three)) (Succ (Succ (Succ (Zero)))))
(def-fns _ $ (many decide : -> (many (Dec three u8-modulus) d)) (lt-dec three u8-modulus))
(let ((many d)) (native-compute decide))
(comptime-match many d (Yes a b p))
(let ((many x)) (MkU8 three p))

(let-match many x (MkU8 xn xq))
(coerce x (coercible-sym (coercible-wrap (Shared) MkU8 xn xq)))
