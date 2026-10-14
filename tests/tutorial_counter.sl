; expect: (MkCounter 2)
(def-adts $ (Counter : -> Type)
  enum
  (many MkCounter : (many (Nat) n) -> (Counter)))

(def-fns _ $ (many bump : (unique (Counter) c) -> (unique (Counter) d at c))
  (match unique c _
    ((MkCounter n cell) (cell (nat-add n 1)))))

(let ((unique c0)) (MkCounter 0))
(let ((unique c1)) (bump c0))
(let ((unique c2)) (bump c1))
(share c2)
