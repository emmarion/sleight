; error: do not canonicalize equally
; distinct only discharges a context that has already equated its two literals.

(let (erased q) (distinct 3 4))
(Zero)
