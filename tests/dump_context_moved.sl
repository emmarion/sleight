(let ((unique u)) (MkPair _ _ 1 2))
(let ((many s)) 5)
(def-unique _ $ (unique f : -> (unique (Pair (Nat) (Nat)) p))
  (let ((unique k)) u)
  (let ((many t)) s)
  (dump-context))
; error: t : (Nat)  [many, Settled, value, bound at tests/dump_context_moved.sl:5:9]
; error: k : (Pair (Nat) (Nat))  [unique, Hypothetical, value, bound at tests/dump_context_moved.sl:4:9]
