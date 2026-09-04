; exit: 8
; One factory called twice: the two closures capture different values under the same parameter, so
; extraction must embed each closure's own captured value (ASSUMPTIONS.md 61).

(def-lvl F)
(def-fns F $ many adder : (many (Nat) n) -> (erased (Level) L) (many (Fn L (many (Nat) m) -> (many (Nat) r)) add-n)
  (def-lvl L)
  (let (erased nl) (prove-predates nat-lvl L))
  (def-fns L $ many add-n : (many (Nat) m) -> (many (Nat) r)
    (nat-add (predates nl) n m))
  (values L add-n))

(let (erased A) (many add2) (adder 2))
(let (erased B) (many add5) (adder 5))
(def-lvl P)
(let (erased ap) (prove-predates A P))
(let (erased bp) (prove-predates B P))
(let (erased np) (prove-predates nat-lvl P))
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(def-fns P $ many k : (many (Maybe (String)) line) -> (many (IO P) next)
  (let (many n) (add2 (predates ap) (add5 (predates bp) 1)))
  (match many (lt-dec (predates np) n u8-modulus) (((IO P) next))
    ((Yes a b p) (Exit P (MkU8 n p)))
    ((No a b q) (Exit P code0))))

(ReadLine P k)
