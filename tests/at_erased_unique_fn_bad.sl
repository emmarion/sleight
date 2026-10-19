; error: is taken at `unique` here; write `(at unique (...))`
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(let ((unique c)) (MkBox 5))
(def-unique _ $ (unique at k : -> (unique (Box) r at c)) c)
(let ((erased k2)) k)
(open-at-fn (at-fn-of k))
(let ((unique a)) (at erased (k2)))
(let ((unique b)) (at erased (k2)))
(values)
