; expect: 7
; The delegate annotation puts a function at the one it delegates to (section 41), so it may stand for a parameter written `at` that one.
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m)) n)
(def-fns _ $ (many g at f : (many (Nat) n) -> (many (Nat) m)) (delegate (f n)))
(def-fns _ $ (many same : (many (Fn (level-of f) (many (Nat) n) -> (many (Nat) m)) a)
    (many (Fn (level-of g) (many (Nat) n) -> (many (Nat) m)) b at a) ->) (values))
(let () (same f g))
(g 7)
