(let ((erased p)) (coercible-ctor _ Cons (Nat) (Nat)))
(Zero)
; error: tests/msg_coercible_ctor_cons_arity_bad.sl:1:19: error: `coercible-ctor` of `Cons` expects 4 more arguments, got 2: expected a source and a target for each erased field and a `Coercible` proof for each other field, in the order of `(erased Type A) (many A head) (many (List A) rest)`
; error: lib/prelude.sl:<**>: note: value constructor `Cons` is declared here
