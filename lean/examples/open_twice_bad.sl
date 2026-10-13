
(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m) (erased (Eq (T) (C) (D)) p) -> (many (Nat) n))
  (let-match erased p (Refl A x))
  (open-adt erased m)
  (Zero))
f
