; expect: 3
(def-adts $ (W : (Type P) -> Type) enum newtype
  (many MkW : (erased Type P) (many (Nat) n) -> (W P))
  (erased Ghost : (erased Type P) -> (W P)))
(def-fns _ $ (many at reindex : (erased Type P) (erased Type Q) (many (W P) x) -> (many (W Q) y at x))
  (match many x _
    ((MkW _ n) (MkW Q n))
    ((Ghost _ u) (u Q))))
(def-fns _ $ (erased ghost : (erased Type P) -> (erased (W P) w))
  (let ((erased c)) (cell-alloc Ghost))
  (c P))
(match many (reindex (Nat) (Bool) (MkW (Nat) 3)) (((Nat) r))
  ((MkW _ n) n)
  ((Ghost _) 0))
