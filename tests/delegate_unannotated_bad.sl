; error: `g` delegates to `inc`, so its header must name the callee: write `at` and the callee after the name
; A `delegate`-bodied function names its callee on its header (section 41).
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many g : (many (Nat) n) -> (many (Nat) m)) (delegate (inc n)))
