; expect: 3
(def-adts $ (Box : -> Type) enum newtype (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (many f : (many (Nat) x) -> (many (Box) r0 at x) (many (Nat) r1 at r0))
  (values (MkBox x) x))
(let ((many _) (many n)) (f 3))
n
