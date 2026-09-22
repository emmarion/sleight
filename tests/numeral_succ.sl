; needs: list vec
; expect: (VCons _ _ 0 $ VCons _ _ 0 $ VCons _ _ 0 $ VNil _)
; unary mints one rule relating a literal to a floor under that many successors, folding the prelude's
; one-step numeral-succ proofs with eq-cong-succ and eq-trans: (unary 5 3) gives 5 is (Succ (Succ 3))
; and leaves 4 opaque, so a literal a million above its floor still costs one rule. (unary a) takes
; (Zero) as the floor, which is what makes a literal usable as a Vec's length.

(unary 5 3)
(def-lvl X)
(def-fns X $ (many drop2 : (erased Type A) (many (Vec A 5) v) -> (many (Vec A 3) w))
  (match many v (((Vec A 3) w))
    (absurd VNil)
    ((VCons a m x xs)
      (match many xs (((Vec A 3) w))
        (absurd VNil)
        ((VCons a2 m2 x2 xs2) xs2)))))

(unary 3)
(unary 2)
(unary 1)
(unary 0)
(def-fns X $ (many three-zeros : -> (many (Vec (Nat) 3) xs))
  (VCons (Nat) 2 (Zero) (VCons (Nat) 1 (Zero) (VCons (Nat) 0 (Zero) (VNil (Nat))))))

(three-zeros)
