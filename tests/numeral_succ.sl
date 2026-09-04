; needs: list vec
; expect: (VCons (Zero) (VCons (Zero) (VCons (Zero) (VNil))))
; unary rewrites a literal to successor form through the prelude's numeral-succ, whose BinSucc witness
; the elaborator spells out: (unary a) unfolds all the way to (Zero), (unary a b) only as far as b, so
; a literal a million above its floor still costs one step.

(unary 3)
(def-lvl X)
(def-fns X $ many three-zeros : -> (many (Vec (Nat) 3) xs)
  (VCons (Nat) 2 (Zero) (VCons (Nat) 1 (Zero) (VCons (Nat) 0 (Zero) (VNil (Nat))))))

(unary 1000 999)
(def-fns X $ many first : (erased Type A) (many (Vec A 1000) v) -> (many A x)
  (match many v ((A r))
    (absurd VNil)
    ((VCons a m x xs) x)))

(three-zeros)
