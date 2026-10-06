(let ((erased t)) (List Nat))
(Zero)
; error: tests/msg_argtype_tyctor_hint_bad.sl:1:25: error: argument 1, `A`, of `List`: type mismatch: expected `Type`, got `(TyCtor -> Type)`
; error: lib/prelude.sl:<**>: note: type constructor `List` is declared here
; error: hint: did you mean `(Nat)`?
