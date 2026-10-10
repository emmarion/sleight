; error: cannot infer `__?1` in `(Pair __?1 (Func L (many (Nat) n) -> (many (Nat) m)))`
; The refusal of a `_` left open in a signature names its keywords as any message does.
(let ((many Func)) Fn)
(def-lvl L)
(def-lvl A)
(def-fns A $ (many app : (many (Pair _ (Func L (many (Nat) n) -> (many (Nat) m))) p) -> (many (Nat) r)) (Zero))
(Zero)
