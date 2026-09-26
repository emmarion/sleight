; expect: (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil _)
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons (SlotVacant) (SlotVacant)) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (let-match many xs (Cons _ hd tl) ((Nil _) (cell _ h ys)))
  (let ((unique next)) (cell-alloc Cons))
  (let ((unique cell2)) (cell-write cell (Cons (SlotHolds h) (SlotHolds next))))
  (let ((many r2)) (tail (append-into _ next hd tl ys)))
  (at (cell2 _ h r2)))
(def-fns _ $ (many append-list : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r))
  (let-match many xs (Cons _ hd tl) ((Nil _) ys))
  (let ((unique cell)) (cell-alloc Cons))
  (append-into _ cell hd tl ys))
(def-fns _ $ (many run : -> (many (List (Nat)) r))
  (append-list _ (Cons _ 1 (Cons _ 2 (Nil _))) (Cons _ 3 (Nil _))))
run
