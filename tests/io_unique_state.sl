; stdin: one
; stdin: two
; stdin: three
; exit: 3
; A continuation owns a unique value across steps: the counter is captured at unique by the def-unique each
; step returns, updated in place through its cell when the next line arrives, and read off at the end.
; Under Fn continuations the closure could hold it only shared, and no step could mutate it.

(def-adts $ (Counter : -> Type)
  enum
  (many MkCounter : (many (Nat) n) -> (Counter)))

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns PA $ (many count : (unique (Counter) c) (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) next))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (match many line _
    ((None a)
      (let-match unique c (MkCounter n cell))
      (match many (lt-dec n u8-modulus) _
        ((Yes x y p) (values w1 (Exit P (MkU8 n p))))
        ((No x y q) (values w1 (Exit P code0)))))
    ((Some a s)
      (let ((unique (Counter) c2)) (match unique c _ ((MkCounter n cell) (cell (Succ n)))))
      (def-unique P $ (unique again : (unique (World) v) -> (unique (World) v2 at v) (unique (Program P) next)) (count c2 v))
      (values w1 (Continue P again)))))

(let ((unique (Counter) counter)) (MkCounter 0))
(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) next)) (count counter w))

(Continue P start)
