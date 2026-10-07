; expect: 0
; A signature naming a parameter's slot, instantiated by an erased call (section 20 lets the argument for a
; `many` parameter be erased there): the slot of an erased argument is that argument's erased slot
; (AT_REDESIGN A2), which the code does not yet mint, binding a formal term in its place (HANDOFF).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s))
  (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) -> (many (Nat) r))
  (let ((erased s)) (f x))
  0)
(g 1)
