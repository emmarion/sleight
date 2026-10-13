
(def-lvl X)
(def-fns X $ (many held : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (erased (Eq (T) (C) (D)) p) -> (many (Nat) n))
  (match erased p (((Nat) r))
    ((Refl A x) (open-absurd m _))))

(def-fns X $ (many refuted : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (erased (Eq (T) (C) (D)) p) -> (many (Nat) n))
  (open-adt erased m)
  (match erased p (((Nat) r))
    (absurd Refl)))

