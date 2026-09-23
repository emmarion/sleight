; error: constructor `VNil` has 0 branches
; error: 3 is a numeral literal, opaque to the checker: `(unary a)` gives a literal its `Succ` shape
; A numeral is opaque (LITERALS.md), so a Vec of length 3 does not refute VNil until (unary 3) says
; 3 is (Succ (Succ (Succ (Zero)))). The refusal notes the literal and the forms that reason about it.

(def-adts $ (Vec : ((Nat) n) -> Type)
  enum
  (many VNil : -> (Vec (Zero)))
  (many VCons : (erased (Nat) n) (many (Nat) h) (many (Vec n) t) -> (Vec (Succ n))))
(def-lvl L)
(def-fns L $ (many hd : (many (Vec 3) v) -> (many (Nat) m))
  (match many v _
    ((VCons n h t) h)))
(Zero)
