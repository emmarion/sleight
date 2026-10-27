; error: a function of no parameters
(def-fns _ $ (many decide : (many (Nat) n) -> (many (Dec (Nat) Lt n (Succ $ Zero)) d)) (lt-dec n (Succ $ Zero)))
(native-compute decide)
