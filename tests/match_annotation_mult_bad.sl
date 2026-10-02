(let ((many mm)) many)
(def-fns _ $ (mm f : (mm (Nat) n) -> (mm (Nat) m))
  (match mm n ((mm (Nat) r))
    ((Zero) n)
    ((Succ k) k)))
; error: tests/match_annotation_mult_bad.sl:3:16: error: a match annotation's entries take no multiplicity; drop `mm`
