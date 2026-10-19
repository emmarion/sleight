; error: the body of an at-`cell-match` must erase to nothing, or to a reordering of variables; this one stores, allocates or calls
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many a)) (Zero))
(let ((many b)) (Succ (Succ (Zero))))
(def-fns _ $ (many rebuild :
    (unique (Cell P (slot-of a) (slot-of b)) u) -> (unique (Pair2) r at u))
  (at unique ((cell-match unique u (at (((Cell P (slot-of a) (slot-of b)) v at u)))
    (P s t back) (let ((many k)) (Succ (Succ b))) back) a b)))
(def-fns _ $ (many run : -> (many (Nat) r))
  (let ((unique u)) (cell-alloc (P (slot-of a) (slot-of b))))
  (let ((unique p)) (rebuild u))
  (let-match unique p (P x y back))
  y)
run
