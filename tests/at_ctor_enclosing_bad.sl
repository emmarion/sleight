; error: `at` in a constructor's telescope cannot name `x`, bound by an enclosing telescope still being written
(def-fns _ $ (many f : (many (Nat) x) (erased (ValCtor (many (Nat) y at x) -> (Unit)) c) -> (many (Nat) r))
  x)
