; warns: tests/main_shadow_echo.sl:5:12: warning: declaration of `String` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; stdin: hi
; expect: _
(def-adts ((String : -> Type) enum (many A : -> (String)) (many B : (many (Nat) n) -> (String))))
(def-lvl M)
(def-fns M ((many main : (many (String) in) -> (many (String) out)) in))
main
