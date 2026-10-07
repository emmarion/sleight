; error: `(slot-of x)` is erased, as `x` is, and stands in a non-erased position
(let ((erased x)) (Zero))
(slot-of x)
