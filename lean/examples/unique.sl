(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))

(def-fns _ $ (many bump : (unique (Box) b) -> (unique (Box) r))
  (match unique b (((Box) r))
    ((B n) (B (Succ (share n))))))

(def-unique _ $ (unique once : (many (Nat) k) -> (many (Nat) r))
  (Succ k))

(let ((unique b)) (B (Succ (Zero))))
(let ((unique c)) (bump b))
(let-match unique c (B m))
(let ((many s)) (share m))
(values (once s))
