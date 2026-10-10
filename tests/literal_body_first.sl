; expect: 84
; A literal first met inside a body, whose scope is dropped, and then at the top level: one entry, by its
; stable id, found at run time by the call (section 45).
(def-fns _ $ (many f : -> (many (Nat) n))
  42)
(let ((many x)) 42)
(nat-add x $ f)
