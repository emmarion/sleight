(def-fns _ $ (many id : (many (Nat) a) -> (many (Nat) r)) a)
(def-fns _ $ (many two : (many (Nat) a) (many (Nat) b at a) -> ) (values))
(let ((many y)) 3)
(let () (two (id y) y))
; error: argument 2, `b`, of `two` does not satisfy `at` `__1`
; error: tests/at_target_note_bad.sl:4:14: note: `__1` is the slot of the entry bound here
; warns: tests/at_target_note_bad.sl:2:41: warning: unused `b`; rename it `_b`
