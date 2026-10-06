(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(let ((many a) (many b)) (values (Zero)))
a
; error: tests/msg_let_values_bad.sl:2:26: error: the enclosing `let` expects 2 values, got 1: expected `(many a) (many b)`
; error: tests/msg_let_values_bad.sl:2:6: note: the binders of the enclosing `let` are here
