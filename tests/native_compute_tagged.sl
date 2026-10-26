; expect: (Mid _)
; host-path: yes
(def-adts $ (Three : -> Type) enum (many Lo : -> (Three)) (many Mid : (erased (Nat) n) -> (Three)) (many Hi : -> (Three)))
(def-fns _ $ (many pick : -> (many (Three) t)) (Mid (Zero)))
(native-compute pick)
