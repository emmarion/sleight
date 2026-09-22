; error: conflicting non-erased uses
(def-lvl answer-level)
(def-fns _ $ (many choose : (many (Nat) tag)
    (unique (UniqueFn answer-level -> (many (Nat) r)) f) -> (many (Nat) r))
  ((match many tag (((UniqueFn answer-level -> (many (Nat) r)) g))
    ((Zero)
      (let ((unique consumed)) f)
      f)
    ((Succ n) f))))
