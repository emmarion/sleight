; error: `(erased ...)` is not a statement
; error: hint: `erased` is a multiplicity
; error: hint: usage: (erased <type> <name>)
(def-fns _ ((many f : -> (many (Nat) y)) (erased (Nat) x) 42))
