; error: conflicting non-erased uses
(def-fns _ $ (many drop : (unique (Nat) n) ->)
  (let ((many a)) (share n))
  (values))
(def-fns _ $ (many f : (unique (Nat) n) -> (many (Nat) r))
  (let () (drop n))
  (share n))
(f (Succ (Zero)))
