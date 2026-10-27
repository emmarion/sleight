; exit: 8
; One factory called twice: the two closures capture different values under the same parameter, so
; extraction must embed each closure's own captured value (ASSUMPTIONS.md 61).

(def-lvl F)
(def-fns F $ (many adder : (many (Nat) n) -> (erased (Level) L) (many (Fn L (many (Nat) m) -> (many (Nat) r)) add-n))
  (def-lvl L)
  (let ((erased nl)) (prove-predates nat-lvl L))
  (def-fns L $ (many add-n : (many (Nat) m) -> (many (Nat) r))
    (nat-add (predates nl) n m))
  (values L add-n))

(let ((erased A) (many add2)) (adder 2))
(let ((erased B) (many add5)) (adder 5))
(def-lvl P)
(let ((erased ap)) (prove-predates A P))
(let ((erased bp)) (prove-predates B P))
(let ((erased np)) (prove-predates nat-lvl P))
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(def-unique P $ (unique k : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((many n)) (add2 (predates ap) (add5 (predates bp) 1)))
  (match many (lt-dec (predates np) n u8-modulus) (((World) w2 at w) ((Program P) p))
    ((Yes _ _ _ _ p) (values w (Exit P (MkU8 n p))))
    ((No _ _ _ _ _) (values w (Exit P code0)))))

(Continue P k)
; warns: tests/io_factory_twice.sl:10:14: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_factory_twice.sl:23:45: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_factory_twice.sl:23:25: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_factory_twice.sl:24:23: warning: unnecessary `(predates _)`; drop it
