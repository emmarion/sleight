(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(let ((erased p)) (coercible-ctor _ Nil (Nat)))
(Zero)
; error: tests/msg_coercible_ctor_arity_bad.sl:2:19: error: `coercible-ctor` of `Nil` expects 2 more arguments, got 1: expected a source and a target for each erased field and a `Coercible` proof for each other field, in the order of `(erased Type A)`
; error: lib/prelude.sl:<**>: note: value constructor `Nil` is declared here
