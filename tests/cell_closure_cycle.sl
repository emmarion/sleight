; needs: cell_closure_cycle_seed
; expect: _
(def-fns _ $ many cyclic : -> (many (Slot) r) s)
(let (many fs) (SlotHolds cyclic))
(let (many n) (u fs))
cyclic
