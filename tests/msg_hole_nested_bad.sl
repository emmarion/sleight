(def-fns _ $ (many k : (erased (List (Nat)) xs) -> (many (Nat) r)) (Zero))
(k (Cons _ _ (Nil _)))
; error: tests/msg_hole_nested_bad.sl:2:4: error: argument 1, `xs`, of `k`: cannot infer `__?1` in `(Cons (Nat) __?1 (Nil (Nat)))`
; error: tests/msg_hole_nested_bad.sl:2:12: note: `__?1` is the `_` written here
; error: tests/msg_hole_nested_bad.sl:1:14: note: function `k` is declared here
