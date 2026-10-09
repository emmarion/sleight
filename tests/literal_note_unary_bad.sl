; error: this `match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `VNil`, which is declared here
; error: 3 in `(Vec 3)` is a numeral literal, opaque to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more
; A numeral is opaque (DESIGN.md section 45), so a Vec of length 3 does not refute VNil until (unary 3) says
; 3 is (Succ (Succ (Succ (Zero)))): forcing the VNil branch binds 3 to (Zero) instead, and the refusal notes
; the literal and the forms that reason about it.

(def-adts $ (Vec : ((Nat) n) -> Type)
  enum
  (many VNil : -> (Vec (Zero)))
  (many VCons : (erased (Nat) n) (many (Nat) h) (many (Vec n) t) -> (Vec (Succ n))))
(def-lvl L)
(def-fns L $ (many hd : (many (Vec 3) v) -> (many (Nat) m))
  (match many v _
    ((VCons n h t) h)))
(Zero)
