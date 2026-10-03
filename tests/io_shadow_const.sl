; warns: tests/io_shadow_const.sl:4:12: warning: declaration of `IO` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; expect: (A)
(def-adts ((IO : -> Type) enum (many A : -> (IO))))
(A)
