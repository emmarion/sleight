; error: cannot infer `_?1` in `(V (Succ _?1))`
; The explicit ValCtor former closes its return type at the same boundary.
(def-adts $ (V : ((Nat) n) -> Type) enum)
(let ((erased C)) (ValCtor (erased (Nat) k) -> (V (Succ _))))
