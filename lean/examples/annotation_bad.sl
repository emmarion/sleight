; `_` as a match annotation needs a position that fixes the telescope
(let ((many a))
  (match many (Zero) _
    ((Zero) (Zero))
    ((Succ k) k)))
a
