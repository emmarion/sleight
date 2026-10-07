; expect: (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil _)
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons vacant-slot vacant-slot) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (let-match many xs (Cons _ hd tl) ((Nil _) (share (cell _ h ys))))
  (let ((unique next)) (cell-alloc Cons))
  (let ((unique cell2)) (cell-write unique cell (Cons (slot-of h) (slot-of next))))
  (let ((many r2)) (tail (append-into _ next hd tl ys)))
  (share (at (cell2 _ h r2))))
(def-fns _ $ (many append-list : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r))
  (let-match many xs (Cons _ hd tl) ((Nil _) ys))
  (let ((unique cell)) (cell-alloc Cons))
  (append-into _ cell hd tl ys))
(def-fns _ $ (many run : -> (many (List (Nat)) r))
  (append-list _ (Cons _ 1 (Cons _ 2 (Nil _))) (Cons _ 3 (Nil _))))
run
