; expect: 12
; As at_argument_word.sl, with the call an entry of a `values` whose later entry has a temporary of its own;
; the first entry's code is bound under both temporaries.
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many f : (many (Nat) y) -> (many (Nat) r at x)) x)
  f)
(def-fns _ $ (many use : (many (Nat) n) -> (many (Nat) r))
  (let ((many g) (many h)) (values (mk (Succ n)) (mk (Succ (Succ n)))))
  (nat-add (g 1) (h 2)))
(let ((many g) (many h)) (values (mk (Succ 1)) (mk (Succ 2))))
(nat-add (use 2) (nat-add (g 0) (h 0)))
