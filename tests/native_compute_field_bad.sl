; error: has a non-erased one
(def-fns _ $ (many two : -> (many (Nat) n)) (Succ $ Succ $ Zero))
(native-compute two)
