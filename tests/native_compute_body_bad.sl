; error: confined to run position
(def-fns _ $ (many decide : -> (many (Dec (Zero) (Succ $ Zero)) d)) (lt-dec (Zero) (Succ $ Zero)))
(def-fns _ $ (many inner : -> (many (Dec (Zero) (Succ $ Zero)) d)) (native-compute decide))
