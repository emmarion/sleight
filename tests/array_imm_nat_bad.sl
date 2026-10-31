; error: type mismatch: expected `(Imm (Copy (Nat)) (MkCopy (Nat) n))`, got `(Imm (Copy (Nat)) (MkCopy (Nat) 5))`
(def-fns _ $ (erased imm-copy-nat : (erased (Nat) v) (erased (Lt v u62-modulus) p) -> (erased (Imm (Copy (Nat)) (MkCopy (Nat) v)) r))
  (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkCopy (Nat) v) (ImmNat v p)))

(def-fns _ $ (many f : (many (Nat) n) (erased (Lt 5 u62-modulus) p5) -> (many (Nat) r))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ n) $ Cons _ (MkCopy _ 5) $ Nil _)))
  (let ((unique old) (erased _) (unique _) (erased _))
    (array-swap-imm _ _ a (Zero) (MkCopy _ 5) _ (NthHere _ _ _) (imm-copy-nat 5 p5) (imm-copy-nat 5 p5)))
  (let-match unique old (MkCopy _ o))
  o)
