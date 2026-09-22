; error: conflicting non-erased uses
(def-adts $ (Ghost : -> Type) union (erased G : -> (Ghost)))
(def-fns _ $ (many twice : (erased (Ghost) g) (unique (Nat) x) -> (unique (Nat) r))
  (let ((unique y)) (match erased g (((Nat) r)) ((G) x)))
  x)
