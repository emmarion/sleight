(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) (erased (Lt a b) p) -> (many (Nat) r)) a)
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) (erased (Lt a b) lt) -> (many (Nat) r)) (f a b _))
(Zero)
; error: tests/msg_hole_hint_bad.sl:2:101: error: argument 3, `p`, of `f` is `_` and cannot be inferred
; error: tests/msg_hole_hint_bad.sl:2:101: note: `__?1` is the `_` written here
; error: tests/msg_hole_hint_bad.sl:2:101: hint: `__?1` has type `(Lt a b)`, as does:
; error: tests/msg_hole_hint_bad.sl:2:54: hint: `lt`, bound here
; warns: tests/msg_hole_hint_bad.sl:1:39: warning: `b` is referenced only in erased positions; declare it `erased`, or rename it `_b`
; warns: tests/msg_hole_hint_bad.sl:1:54: warning: unused `p`; rename it `_p`
