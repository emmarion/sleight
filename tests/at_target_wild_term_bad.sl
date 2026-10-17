; error: argument 2, `m`, of `f` does not satisfy `at`
; error: is the slot of the `_` written here
(def-fns _ $ (many f : (erased (Nat) n) (erased n is m at n) -> ) (values))
(let ((erased x)) 3)
(let () (f _ (Succ x)))
; warns: tests/at_target_wild_term_bad.sl:3:41: warning: unused `m`; rename it `_m`
