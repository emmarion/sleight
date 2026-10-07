; expect: 1
; A parameter written `at` holds its target's word inside the body (AT_REDESIGN A3), whichever parameter the
; target is: the body returns it as a plain result.
(def-fns _ $ (many second : (many (Nat) m) (many (Nat) n at m) -> (many (Nat) r))
  n)
(def-fns _ $ (many go : (many (Nat) n) -> (many (Nat) r))
  (second n n))
(go 1)
