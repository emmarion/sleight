; error: error: argument 1, `x`, of `f`: type mismatch: expected `(Nat)`, got `(_<**>)`
; A numeral is the prelude's Nat, not the Nat that shadows it.

(def-adts $ (Nat : -> Type) enum (many A : -> (Nat)))
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) r)) x)
(f 3)
; warns: tests/literal_shadow_arg_bad.sl:4:13: warning: declaration of `Nat` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
