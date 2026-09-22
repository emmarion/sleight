; expect: _
(def-adts $ (NodeT : -> Type) enum (many Node : (many (Slot) s) -> (NodeT)) (many End : -> (NodeT)))
(let ((unique u)) (cell-alloc Node))
(let ((many s)) (SlotHolds u))
s
