; needs: list vec
; expect: (VCons _ _ 0 $ VNil _)
; Transport along a user-defined equality needs no substitution principle: matching NatRefl forces the two
; indices to canonicalize together, and v's type becomes the result type in that branch.

(def-adts $ (NatEq : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many NatRefl : (erased (Nat) x) -> (NatEq x x)))

(def-lvl V)
(def-fns V $ (many cast : (erased (Nat) a) (erased (Nat) b) (erased (NatEq a b) e) (many (Vec (Nat) a) v) -> (many (Vec (Nat) b) w))
  (match erased e _
    ((NatRefl _) v)))

(let ((many one)) (Succ (Zero)))
(cast one one (NatRefl one) (VCons (Nat) (Zero) (Zero) (VNil (Nat))))
