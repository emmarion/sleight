; expect: (Lo)
; host-path: yes
(def-adts $ (Three : -> Type) enum (many Lo : -> (Three)) (many Mid : (erased (Nat) n) -> (Three)) (many Hi : -> (Three)))
(def-fns _ $ (many pick : -> (many (Three) t)) (Mid (Zero)))
(def-fns _ $ (many low : -> (many (Three) t)) (Lo))
(let ((many three)) (Succ (Succ (Succ (Zero)))))
(def-fns _ $ (many decide : -> (many (Dec (Nat) Lt three u8-modulus) d)) (lt-dec three u8-modulus))
(let ((many a) (many d) (many b)) (native-compute pick decide low))
(comptime-match many a (Mid _))
(comptime-match many d (Yes _ _ _ _ _))
b
