; needs: list vec
; expect: (VCons _ _ 0 $ VCons _ _ 0 $ VCons _ _ 0 $ VNil _)
; A numeral is an opaque Nat with a Numeral proof relating it to its bijective base-2 spelling; unfolding
; that proof by erased matches makes the literal unary-known inside the branch, here to index a Vec by 3.

(def-lvl X)
(def-fns X $ (many three-zeros : (erased (Nat) n) (erased (Numeral (B1 (B1 (BZ))) n) v) -> (many (Vec (Nat) n) xs))
  (let-match erased v (N1 _ _ d v1 dd) (absurd NZ) (absurd N2))
  (let-match erased v1 (N1 _ _ _ v0 dd0) (absurd NZ) (absurd N2))
  (let-match erased v0 (NZ) (absurd N1) (absurd N2))
  (let-match erased dd0 (D0) (absurd DS))
  (let-match erased dd (DS _ b1 dd1) (absurd D0))
  (match erased dd1 _
    ((D0) (VCons (Nat) d 0 (VCons (Nat) (Succ b1) 0 (VCons (Nat) b1 0 (VNil (Nat))))))
    (absurd DS)))

(three-zeros 3 (numeral-of 3))
