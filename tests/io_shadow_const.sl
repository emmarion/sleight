; expect: (A)
(def-adts ((Program : -> Type) enum (many A : -> (Program))))
(A)
; warns: tests/io_shadow_const.sl:2:12: warning: declaration of `Program` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
