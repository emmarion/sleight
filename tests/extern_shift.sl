; expect: (Cons _ 40 $ Cons _ 20 $ Cons _ 40 $ Cons _ 5 $ Cons _ 0 $ Nil _)
; Nat shifts (section 41): shl and shr return the Pow2 and Mul or quotient proofs, nat-shl and nat-shr drop them.

(let ((many a) (erased v1) (erased p1) (erased m1)) (shl 5 3))
(let ((many b) (erased v2) (erased p2) (erased m2) (erased r2) (erased mm2) (erased a2) (erased l2)) (shr a 1))
(Cons _ a $ Cons _ b $ Cons _ (nat-shl 5 3) $ Cons _ (nat-shr 41 3) $ Cons _ (nat-shr 3 2) $ Nil _)
