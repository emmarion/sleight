; error: argument 2, `y`, of `f` does not satisfy `at` `(slot-of a)`
(def-fns _ $ (many f : (erased (Nat) x) (erased (Nat) y at x) -> (many (Nat) r)) 0)
(def-fns _ $ (many g : (erased (Nat) a) (erased (Nat) b) -> (many (Nat) r)) (f a b))
; warns: tests/at_erased_param_bad.sl:2:41: warning: unused `y`; rename it `_y`
