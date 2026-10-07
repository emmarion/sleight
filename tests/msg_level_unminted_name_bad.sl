(def-fns _ $ (many factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (many (Nat) x) -> (many (Nat) y)) h))
  (def-fns _ $ (many h : (many (Nat) x) -> (many (Nat) y)) x)
  (values (level-of h) h))
(def-fns _ $ (many base : (many (Nat) x) -> (many (Nat) y)) x)
(let ((erased L) (many hh)) (factory (level-of base)))
(def-fns _ $ (many top : (many (Nat) x) -> (many (Nat) y)) x)
(def-fns L $ (many caller : (many (Nat) x) -> (many (Nat) y)) (top x))
; error: tests/msg_level_unminted_name_bad.sl:9:63: error: `L` is not a level minted by `def-lvl`
