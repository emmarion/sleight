; stderr: real
; exit: 1
(let ((erased RealProgram)) Program)
(def-adts ((Program : -> Type) enum (many A : -> (Program))))
(def-lvl P)
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (RealProgram P) p))
  (let ((unique w1) (many _)) (world-do _ w (WriteErr "real\n")))
  (values w1 (Exit P code1)))
(let ((unique (RealProgram P) prog)) (Continue P start))
prog
; warns: tests/io_shadow_keep_real.sl:4:12: warning: declaration of `Program` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
