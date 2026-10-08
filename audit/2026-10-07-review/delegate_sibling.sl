(def-fns _ $ (many ident : (many (Nat) x) -> (many (Nat) r)) x)
(def-fns _
  ((many first : (many (Nat) x) -> (many (Nat) r)) (delegate (ident x)))
  ((many second : (many (Nat) x) -> (many (Nat) r))
    (let ((erased p)) (delegate-of first))
    x))
(second 0)
