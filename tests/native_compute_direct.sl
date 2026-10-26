; expect: (MkU8 3 _)
; host-path: yes
(let ((many three)) (Succ (Succ (Succ (Zero)))))
(def-fns _ $ (many decide : -> (many (Dec three u8-modulus) d)) (lt-dec three u8-modulus))
(comptime-match many (native-compute decide) (Yes a b p))
(MkU8 three p)
