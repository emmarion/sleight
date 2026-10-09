; error: tests/open_adt_erased_pos_bad.sl:3:3: error: an `open-adt` written `many` in an erased position; write `erased` here
(def-fns _ $ (erased ghost : (many (Matchable enum List (many Nil) (many Cons)) m) -> (erased (Nat) r))
  (open-adt many m)
  (Zero))
(Zero)
