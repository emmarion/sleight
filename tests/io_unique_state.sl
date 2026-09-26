; stdin: one
; stdin: two
; stdin: three
; exit: 3
; A continuation owns a unique value across requests: the counter is captured at unique by the def-unique
; each ReadLine wraps, updated in place through its cell when the next line arrives, and read off at the
; end. Under Fn continuations the closure could hold it only shared, and no request could mutate it.

(def-adts $ (Counter : -> Type)
  enum
  (many MkCounter : (many (Nat) n) -> (Counter)))

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((erased nat-p0)) (prove-predates nat-lvl PA))
(let ((erased pa-p)) (prove-predates PA P))

(def-fns PA $ (many count : (unique (Counter) c) (many (Maybe (String)) line) -> (unique (IO P) next))
  (match many line _
    ((None a)
      (let-match unique c (MkCounter n cell))
      (match many (lt-dec (predates nat-p0) n u8-modulus) _
        ((Yes x y p) (Exit P (MkU8 n p)))
        ((No x y q) (Exit P code0))))
    ((Some a s)
      (let ((unique (Counter) c2)) (match unique c _ ((MkCounter n cell) (cell (Succ n)))))
      (def-unique P $ (unique again : (many (Maybe (String)) next-line) -> (unique (IO P) next)) (count (predates pa-p) c2 next-line))
      (ReadLine P again))))

(let ((unique (Counter) counter)) (MkCounter 0))
(def-unique P $ (unique start : (many (Maybe (String)) line) -> (unique (IO P) next)) (count (predates pa-p) counter line))

(ReadLine P start)
