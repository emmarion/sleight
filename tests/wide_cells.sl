; needs: ../std/macro wide_lib
; expect: (Cons _ 2 $ Cons _ 2 $ Cons _ 1 $ Cons _ 7 $ Cons _ 3 $ Cons _ 6 $ Nil _)
; Cells of constructors past OCaml's block tags, which share one OCaml constructor: allocated, invoked,
; written, copied, matched, reused in place, and filled by a loop in destination-passing style.
(def-adts $ (Cel : -> Type)
  enum
  (many Cz : -> (Cel))
  (wide ctors Cel Ce 247 2 (Nat)))

(def-adts $ (WL : -> Type)
  enum
  (many End : -> (WL))
  (many Item : (many (Nat) h) (many (WL) t) -> (WL))
  (wide ctors WL Wx 247 1 (Nat)))

(def-fns _ $ (many swap : (unique (Cel) x) -> (unique (Cel) r at x))
  (match unique x _ ((Ce245 a b u) (u b a)) (else y y)))

(def-fns _ $ (many fill-into : (unique (Cell Item vacant-slot vacant-slot) cell) (many (Nat) h) (subterm many (Nat) n) ->
    (many (WL) r at cell))
  (let-match many n (Succ m) ((Zero) (share (cell h (End)))))
  (let ((unique next)) (cell-alloc Item))
  (let ((unique cell2)) (cell-write unique cell (Item (slot-of h) (slot-of next))))
  (let ((many r2)) (tail (fill-into next m m)))
  (share (at unique (cell2 h r2))))

(def-fns _ $ (many wl-sum : (subterm many (WL) l) -> (many (Nat) r))
  (match many l _ ((Item h t) (nat-add h $ notail $ wl-sum t)) (else 0)))

(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (let ((unique u)) (cell-alloc Ce245))
  (let ((many p)) (share (u 1 2)))
  (let-match many p (Ce245 _ got))
  (let ((many a)) 1)
  (let ((many b)) 2)
  (let ((unique w)) (cell-alloc (Ce245 (slot-of a) (slot-of b))))
  (let ((unique v))
    (cell-match unique w (((Cell Ce245 (slot-of a) (slot-of b)) v at w))
      (Ce245 _ _ back) back))
  (let ((many q)) (share (at unique (v a b))))
  (let-match many q (Ce245 _ two2))
  (let ((many old)) (Ce246 1))
  (let-match many old (Ce246 _ c))
  (let ((unique c2)) (cell-write many c (Ce246 _)))
  (let ((many fresh)) (share (c2 7)))
  (let-match many fresh (Ce246 seven))
  (let-match many old (Ce246 kept))
  (let ((many swapped)) (share (swap (Ce245 4 3))))
  (let-match many swapped (Ce245 swapped-a _) (else (Nil _)))
  (let ((unique start)) (cell-alloc Item))
  (Cons _ got $ Cons _ two2 $ Cons _ kept $ Cons _ seven $ Cons _ swapped-a $ Cons _ (wl-sum $ fill-into start 3 3) $ Nil _))

main
