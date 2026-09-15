; error: undecided
; Whether a Newtype has a contradicting open is not settled (DESIGN.md section 19), so
; open-absurd refuses one; open-adt records a Newtype and asserts nothing of it.

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T) (erased (ValCtor (many (Nat) n) -> (T)) C) (erased (Newtype C) nt) -> (many (Nat) n)
  (open-absurd nt _))
f
