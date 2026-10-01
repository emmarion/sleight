; error: `(level-of f)`, a `Level` and so erased, used in a non-erased position

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m)) n)
(let ((many l)) (level-of f))
