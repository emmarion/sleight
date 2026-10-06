(def-fns _ $ (many k : (erased (List (Nat)) xs) -> (many (Nat) r)) (Zero))
(k (Cons _ (Succ _) (Nil _)))
; error: tests/msg_hole_nested_deep_bad.sl:2:4: error: argument 1, `xs`, of `k`: cannot infer `_?1` in `(Cons (Nat) (Succ _?1) (Nil (Nat)))`
; error: tests/msg_hole_nested_deep_bad.sl:2:18: note: `_?1` is the `_` written here
; error: tests/msg_hole_nested_deep_bad.sl:1:14: note: function `k` is declared here
