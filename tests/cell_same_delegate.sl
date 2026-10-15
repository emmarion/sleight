; expect: 7
(def-fns _ $ (many g : (many (Nat) h) (many (List (Nat)) t) (many (Cell Cons (slot-of h) (slot-of t)) u) -> (many (Nat) r)) h)
(def-fns _ $ (many f at g : (many (Nat) h) (many (List (Nat)) t) (many (Cell Cons (slot-of h) (slot-of t)) u) -> (many (Nat) r))
  (let ((many s)) (cell-same u u))
  (delegate (g h t u)))
(def-fns _ $ (many run : (many (List (Nat)) xs) -> (many (Nat) r))
  (let-match many xs (Cons _ h t u) ((Nil _) 0))
  (f h t u))
(run (Cons _ 7 (Nil _)))
