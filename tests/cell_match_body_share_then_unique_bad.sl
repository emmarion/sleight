; error: unique value `x` has conflicting non-erased uses
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many eat : (unique (Box) b) -> (many (Nat) n)) (let-match unique b (MkBox n _)) n)
(def-fns _ $ (many f : (unique (Box) x) (many (Box) y) -> (many (Nat) n) (many (Box) z))
  (let-match many y (MkBox m u))
  (let ((many a) (many z)) (cell-match many u (((Nat) r) ((Box) z)) (MkBox s) (values 0 (share x))))
  (values (eat x) z))
