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
(let (erased u8p) (prove-predates u8-lvl P))
(def-fns P $ many k : (many (Maybe (String)) line) -> (many (IO P) next)
  (Exit P (nat-to-u8 (predates u8p) (add2 (predates ap) (add5 (predates bp) 1)))))

(ReadLine P k)
