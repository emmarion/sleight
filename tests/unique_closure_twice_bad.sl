; error: conflicting non-erased uses
(def-unique _ $ (unique once : -> (unique (Nat) r)) (Zero))
(let ((unique x)) (once))
(let ((unique y)) (once))
