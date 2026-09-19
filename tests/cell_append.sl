; expect: (Cons 1 (Cons 2 (Cons 3 (Nil))))
(def-fns _ $ many append-into : (erased Type A)
    (unique (Cell Cons (SlotVacant) (SlotVacant)) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell)
  (match many xs _
    ((Nil _) (cell _ h ys))
    ((Cons _ hd tl)
      (let (unique next) (cell-alloc Cons))
      (let (unique cell2) (cell-write cell (Cons (SlotHolds h) (SlotHolds next))))
      (let (many r2) (tail (append-into _ next hd tl ys)))
      (at (cell2 _ h r2)))))
(def-fns _ $ many append-list : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r)
  (match many xs _
    ((Nil _) ys)
    ((Cons _ hd tl)
      (let (unique cell) (cell-alloc Cons))
      (append-into _ cell hd tl ys))))
(def-fns _ $ many run : -> (many (List (Nat)) r)
  (append-list _ (Cons _ 1 (Cons _ 2 (Nil _))) (Cons _ 3 (Nil _))))
run
