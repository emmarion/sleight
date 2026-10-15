; expect: (EONonErased _ _)
(let ((many xs)) (Cons _ 7 (Nil _)))
(let-match many xs (Cons _ h1 t1 u1))
(let-match many xs (Cons _ h2 t2 u2))
(let ((many s)) (cell-same u1 u2))
(comptime-match many s (EONonErased _ e))
(let-match erased e (JMRefl _ _))
(let ((erased (Eq (Slot) (slot-of h1) (slot-of h2)) q)) (Refl (Slot) (slot-of h1)))
s
