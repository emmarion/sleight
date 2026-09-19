; error: contradicts nothing

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T) (erased (ValCtor (many (Nat) n) -> (T)) C) (erased (Matchable enum newtype T (many C)) nt) -> (many (Nat) n)
  (open-absurd nt _))
f
