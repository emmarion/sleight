; error: tests/share_erased_let_bad.sl:3:21: error: `share` in an erased position
(def-fns _ $ (erased drop : (unique (Nat) n) -> (erased (Nat) r))
  (let ((erased m)) (share n))
  m)
(Zero)
