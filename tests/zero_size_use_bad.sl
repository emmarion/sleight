; error: conflicting non-erased uses
; error: tests/zero_size_use_bad.sl:7:17: note: already used at unique here
(def-fns _ $ (many drop : (unique (Nat) n) ->)
  (let ((many _)) (share n))
  (values))
(def-fns _ $ (many f : (unique (Nat) n) -> (many (Nat) r))
  (let () (drop n))
  (share n))
(f (Succ (Zero)))
