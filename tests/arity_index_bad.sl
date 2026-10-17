(def-fns _ $ (many v : (erased (Nat) n) (many (Vec (Nat) n) xs) (many (Nat) i) -> (many (Nat) y)) i)
(v (Succ (Zero)) (VNil (Nat)))
; needs: vec
; error: tests/arity_index_bad.sl:2:1: error: `v` expects 3 arguments, got 2: expected `(erased (Nat) n) (many (Vec (Nat) n) xs) (many (Nat) i)`
; error: tests/arity_index_bad.sl:1:14: note: function `v` is declared here
; warns: tests/arity_index_bad.sl:1:41: warning: unused `xs`; rename it `_xs`
