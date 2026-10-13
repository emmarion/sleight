(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))

(def-fns _ $ (many move : (unique (Nat) x) -> (unique (Nat) r at x)) x)

(def-fns _ $ (many fill : (many (Nat) n) -> (many (Pair2) p))
  (let ((unique u)) (cell-alloc (P (slot-of n) _)))
  (share (u (at) n (Succ n))))

(let ((unique y)) (move (Succ (Succ (Succ (Zero))))))
(let-match many (fill (share y)) (P a b))
b
