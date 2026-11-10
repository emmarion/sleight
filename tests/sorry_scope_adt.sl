; In a tainted scope the constructors a `def-adts` binds are tainted, so a `comptime-match` on a value one of
; them built checks no value, and a `native-compute` there compiles and runs nothing.
; host-path: yes
(let ((erased e)) (sorry (((Eq (Nat) 1 1) q))))
(let-match erased e (Refl _ _))
(def-adts $ (Col : -> Type) enum (many Red : -> (Col)) (many Blue : -> (Col)))
(let ((many c)) (Red))
(comptime-match many c (Red))
(def-fns _ $ (many pick : -> (many (Col) k)) (Blue))
(let ((many d)) (native-compute pick))
(match many d (((Nat) r)) ((Red) 1) ((Blue) 2))
; expect: sorry
; warns: tests/sorry_scope_adt.sl:4:19: warning: this unit uses `sorry` once, here; nothing that depends on it runs
