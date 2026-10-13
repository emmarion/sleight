; error: `at` is allowed only on function telescope and match annotation entries
; A value constructor's field cannot be written `at`; a field placed at a slot holds a `Placed` value instead.
(def-fns _ $ (many f : (many (Nat) x) (erased (ValCtor (many (Nat) y at x) -> (Unit)) c) -> (many (Nat) r))
  x)
