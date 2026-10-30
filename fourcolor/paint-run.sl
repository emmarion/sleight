; Runs paint.sl's search on a straight-line drawing of K4 and checks the colours it finds. Load after paint.sl.

(def-fns _ $ (many paints-of : (many (List (Edge)) es) -> (many (List (Paint)) ks))
  (let ((many qs) (erased pd)) (paint-ends (Nil (Paint)) es))
  (match many (paint-go es qs (Nil (Paint)) (B4Nil) pd) _
    ((PaintFound _ _ ks _ _) ks)
    ((PaintNone _ _ _) (Nil (Paint)))))

(let ((many o) (many p) (many q) (many r)) (values (MkPoint 0 0) (MkPoint 4 0) (MkPoint 2 4) (MkPoint 2 1)))
(let ((many k4)) (Cons (Edge) (MkEdge o p) $ Cons (Edge) (MkEdge o q) $ Cons (Edge) (MkEdge o r) $
  Cons (Edge) (MkEdge p q) $ Cons (Edge) (MkEdge p r) $ Cons (Edge) (MkEdge q r) $ Nil (Edge)))
(let ((many ks)) (paints-of k4))
(comptime-match many ks (Cons _ k1 ks1))
(comptime-match many ks1 (Cons _ k2 ks2))
(comptime-match many ks2 (Cons _ k3 ks3))
(comptime-match many ks3 (Cons _ k4 ks4))
(comptime-match many ks4 (Nil _))
ks
