; error: conflicting non-erased uses
(def-fns _ $ (many joined : (many (Nat) tag) (unique (Nat) x) -> (unique (Nat) r))
  (let ((unique y)) (match many tag (((Nat) r)) ((Zero) x) ((Succ k) (Zero))))
  x)
