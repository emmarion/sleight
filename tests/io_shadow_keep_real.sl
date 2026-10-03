; warns: tests/io_shadow_keep_real.sl:6:12: warning: declaration of `IO` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; stderr: real
; exit: 1
(let ((erased RealIO)) IO)
(def-adts ((IO : -> Type) enum (many A : -> (IO))))
(def-lvl P)
(let ((erased thunk-p)) (prove-predates thunk-lvl P))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(def-unique P $ (unique after : (many (Result (String)) r) -> (unique (RealIO P) next))
  (WriteErr P "real\n" (unique-thunk (predates thunk-p) _ _ (Exit P code1))))
(let ((unique (RealIO P) prog)) (ReadFile P "no-such-file" after))
prog
