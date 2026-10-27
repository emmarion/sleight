; expect: (MkU8 3 _)
; host-path: yes
(let ((many three)) (Succ (Succ (Succ (Zero)))))
(def-fns _ $ (many decide : -> (many (Dec (Nat) Lt three u8-modulus) d)) (lt-dec three u8-modulus))
(comptime-match many (native-compute decide) (Yes _ _ a b p))
(MkU8 three p)
