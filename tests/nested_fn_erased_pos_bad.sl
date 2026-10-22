; error: tests/nested_fn_erased_pos_bad.sl:3:16: error: a `def-fns` function written `many` in an erased position; write `erased` here
(def-fns _ $ (erased peek : (erased (Nat) n) -> (erased (Nat) r))
  (def-fns _ $ (many g : (many (Nat) k) -> (many (Nat) j)) (Succ k))
  n)
(Zero)
