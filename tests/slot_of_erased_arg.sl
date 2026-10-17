; expect: 0
; A signature naming a parameter's slot, instantiated by an erased call (section 14 lets the argument for a
; `many` parameter be erased there): the slot of an erased argument is that argument's erased slot (section 35).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s))
  (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) -> (many (Nat) r))
  (let ((erased _)) (f x))
  0)
(g 1)
