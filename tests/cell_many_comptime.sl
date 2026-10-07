; expect: 5
; A `comptime-match` at `many` binds a Const cell (AT_REDESIGN A8), and a write into it copies.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(let ((many b)) (MkBox 1))
(comptime-match many b (MkBox n u))
(let ((unique u2)) (cell-write u (MkBox _)))
(let ((many c)) (u2 5))
(let-match many c (MkBox m))
m
