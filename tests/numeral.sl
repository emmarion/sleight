; needs: list vec
; expect: (VCons _ _ 0 $ VCons _ _ 0 $ VCons _ _ 0 $ VNil _)
; A numeral is an opaque Nat with a Numeral proof relating it to its bijective base-2 spelling; unfolding
; that proof by erased matches makes the literal unary-known inside the branch, here to index a Vec by 3.

(def-lvl X)
(def-fns X $ many three-zeros : (erased (Nat) n) (erased (Numeral (B1 (B1 (BZ))) n) v) -> (many (Vec (Nat) n) xs)
  (match erased v _
    (absurd NZ)
    (absurd N2)
    ((N1 b m d v1 dd)
      (match erased v1 _
        (absurd NZ)
        (absurd N2)
        ((N1 b0 m0 d0 v0 dd0)
          (match erased v0 _
            ((NZ)
              (match erased dd0 _
                ((D0)
                  (match erased dd _
                    (absurd D0)
                    ((DS a b1 dd1)
                      (match erased dd1 _
                        ((D0) (VCons (Nat) d 0 (VCons (Nat) (Succ b1) 0 (VCons (Nat) b1 0 (VNil (Nat))))))
                        (absurd DS)))))
                (absurd DS)))
            (absurd N1)
            (absurd N2)))))))

(three-zeros 3 (numeral-of 3))
