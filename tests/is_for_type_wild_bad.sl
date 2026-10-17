; error: argument 2, `f`, of `use`: type mismatch: expected `(Fn L (erased Type A) -> (erased __?1 r))`, got `(Fn L (erased Type A) -> (erased (False) is r))`
(def-lvl L)
(def-fns L $ (erased falsity : (erased Type A) -> (erased (False) is r)) (False))
(def-fns _ $ (erased use : (erased Type B) (erased (Fn L (erased Type A) -> (erased B r)) f) -> (erased B impossible))
  (f (Nat)))
(let ((erased contradiction)) (use _ falsity))
; warns: tests/is_for_type_wild_bad.sl:3:32: warning: unused `A`; rename it `_A`
