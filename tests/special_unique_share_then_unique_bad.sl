; error: conflicting non-erased uses
(def-fns _ $ (many take : (unique (Special) s) -> (many (Nat) r)) (Zero))
(let ((unique u)) (%let))
((share u) ((many x)) (Zero))
(take u)
