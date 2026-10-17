; expect: 14
; As at_argument_word.sl, inside a body: the temporary's binding encloses the statements after the `let`.
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many f : (many (Nat) y) -> (many (Nat) r at x)) x)
  f)
(def-fns _ $ (many use : (many (Nat) n) -> (many (Nat) r))
  (let-match many (Cons (Nat) (Succ n) (Nil (Nat))) (Cons _ hd _))
  (let ((many g)) (mk (Succ hd)))
  (let ((many a)) (g 1))
  (let ((many b)) (g 2))
  (nat-add a b))
(use 5)
