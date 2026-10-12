; error: `(slot-of x)` was not in scope when level `L` was minted
; As tests/slot_of_predates.sl, the slot's entry introduced after the level.
(def-lvl L)
(let ((many x)) 3)
(let ((erased p)) (prove-predates (slot-of x) L))
