; exit: 9
; A factory's parameter holds a closure, and the factory's own closure matches on it: extraction embeds the
; captured data as a named constant between the two closures' let recs (ASSUMPTIONS.md 61).

(def-lvl F)
(def-fns F $ (many adder : (many (Nat) n) -> (erased (Level) L) (many (Fn L (many (Nat) m) -> (many (Nat) r)) add-n))
  (def-lvl L)
  (let ((erased nl)) (prove-predates nat-lvl L))
  (def-fns L $ (many add-n : (many (Nat) m) -> (many (Nat) r))
    (nat-add (predates nl) n m))
  (values L add-n))

(let ((erased A) (many add2)) (adder 2))

(def-lvl G)
(def-fns G $ (many applier : (many (Nat) k) (many (Maybe (Fn A (many (Nat) m) -> (many (Nat) r))) boxed) ->
    (erased (Level) L) (many (Fn L (many (Nat) x) -> (many (Nat) y)) g))
  (def-lvl L)
  (let ((erased al)) (prove-predates A L))
  (let ((erased nl)) (prove-predates nat-lvl L))
  (def-fns L $ (many g : (many (Nat) x) -> (many (Nat) y))
    (match many boxed (((Nat) r))
      ((None _) x)
      ((Some _ f) (f (predates al) (nat-add (predates nl) k x)))))
  (values L g))

(let ((erased B) (many g3)) (applier 3 (Some (Fn A (many (Nat) m) -> (many (Nat) r)) add2)))
(def-lvl P)
(let ((erased bp)) (prove-predates B P))
(let ((erased np)) (prove-predates nat-lvl P))
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(def-unique P $ (unique k : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) next))
  (let ((many n)) (g3 (predates bp) 4))
  (match many (lt-dec (predates np) n u8-modulus) (((World) w2 at w) ((Program P) next))
    ((Yes _ _ _ _ p) (values w (Exit P (MkU8 n p))))
    ((No _ _ _ _ _) (values w (Exit P code0)))))

(Continue P k)
; warns: tests/io_closure_in_data.sl:10:14: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_closure_in_data.sl:24:45: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_closure_in_data.sl:24:22: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_closure_in_data.sl:35:23: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_closure_in_data.sl:36:23: warning: unnecessary `(predates _)`; drop it
