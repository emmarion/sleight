; needs: list vec
; expect: (VCons _ _ 0 $ VNil _)
; Transport along a user-defined equality needs no substitution principle: matching Refl forces the two
; indices to canonicalize together, and v's type becomes the result type in that branch.

(def-adts $ (Eq : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many Refl : (erased (Nat) x) -> (Eq x x)))

(def-lvl V)
(def-fns V $ (many cast : (erased (Nat) a) (erased (Nat) b) (erased (Eq a b) e) (many (Vec (Nat) a) v) -> (many (Vec (Nat) b) w))
  (match erased e _
    ((Refl x) v)))

(let ((many one)) (Succ (Zero)))
(cast one one (Refl one) (VCons (Nat) (Zero) (Zero) (VNil (Nat))))
