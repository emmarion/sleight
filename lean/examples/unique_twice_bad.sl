(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(def-fns _ $ (many bump : (unique (Box) b) -> (unique (Box) r)) b)
(let ((unique b)) (B (Succ (Zero))))
(let ((unique c)) (bump b))
(let ((unique d)) (bump b))
0
