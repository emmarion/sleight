; error: unique value `x` has conflicting non-erased uses
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many eat : (unique (Box) b) -> (many (Nat) n)) (let-match unique b (MkBox n _)) n)
(def-fns _ $ (many f : (unique (Box) x) (many (Box) y) -> (many (Nat) n))
  (let ((many a)) (match many y (((Nat) r)) ((MkBox m u) (cell-match many u (((Nat) r)) (MkBox s) (eat x)))))
  (eat x))
