(def-fns _ $ (many two : (many (Nat) n) -> (many (Nat) a) (many (Nat) b)) (values n (Succ n)))
(let ((erased a) (many b)) (two 0))
(dump-context)
; error: a : (Nat)  [erased, Const, value, bound at tests/dump_context_dropped.sl:2:7]
; error: __2 : (Nat)  [many, Const, value, anonymous, bound at tests/dump_context_dropped.sl:2:28]
; error: = 0
