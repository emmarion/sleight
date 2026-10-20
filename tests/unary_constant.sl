; needs: list vec
; expect: (VCons _ _ 0 $ VCons _ _ 0 $ VNil _)
; unary takes any Settled `many` Nat or Char, not only a literal, and a floor equal to it walks no successors.

(let ((many two)) (nat-add 1 1))
(unary two)
(unary 7 7)
(unary #\x02 1)
(def-fns _ $ (many two-zeros : -> (many (Vec (Nat) two) xs))
  (VCons (Nat) (Succ (Zero)) (Zero) (VCons (Nat) (Zero) (Zero) (VNil (Nat)))))
(two-zeros)
