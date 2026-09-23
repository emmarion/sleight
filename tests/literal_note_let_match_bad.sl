; error: constructor `VNil` is not refuted, so `Vec` needs an ordinary `match`
; error: 2 is a numeral literal, opaque to the checker
; let-match needs every other constructor refuted, and a literal length refutes none of them.

(def-adts $ (Vec : ((Nat) n) -> Type)
  enum
  (many VNil : -> (Vec (Zero)))
  (many VCons : (erased (Nat) n) (many (Nat) h) (many (Vec n) t) -> (Vec (Succ n))))
(def-lvl L)
(def-fns L $ (many hd : (many (Vec 2) v) -> (many (Nat) m))
  (let-match many v (VCons n h t))
  h)
(Zero)
