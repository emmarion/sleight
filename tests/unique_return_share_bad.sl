; error: the return `m` of `f`, declared `unique`, used at many without `share`

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (unique (Nat) m)) (Succ n))
(let ((many x)) (f (Zero)))
(Zero)
