; error: tests/zero_size_use_bad.sl:3:9: error: a `let` binder written `many` in an erased position; write `erased` here
(def-fns _ $ (many drop : (unique (Nat) n) ->)
  (let ((many _)) (share n))
  (values))
(Zero)
