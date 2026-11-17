(let ((many x)) (Succ (Zero)))
(let ((many r)) (slot-eq (slot-of x) (slot-of x)))
(comptime-match many r (ESome _ e))
r
