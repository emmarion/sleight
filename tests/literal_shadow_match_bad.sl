; error: error: `A` is not a constructor of `Nat`
; A numeral is the prelude's Nat however the program shadows the name, so the shadowing Nat's constructors
; do not match it.

(def-adts $ (Nat : -> Type) enum (many A : -> (Nat)) (many B : (many (Nat) p) -> (Nat)))
(match many 9 (((Bool) r)) ((A) (BTrue)) ((B p) (BFalse)))
; warns: tests/literal_shadow_match_bad.sl:5:13: warning: declaration of `Nat` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
