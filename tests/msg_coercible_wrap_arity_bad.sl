(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(let ((erased p)) (coercible-wrap _ MkCopy (Nat)))
(Zero)
; error: tests/msg_coercible_wrap_arity_bad.sl:2:19: error: `coercible-wrap` of `MkCopy` expects 2 more arguments, got 1: expected `(erased Type A) (erased A v)`
; error: lib/prelude.sl:<**>: note: value constructor `MkCopy` is declared here
