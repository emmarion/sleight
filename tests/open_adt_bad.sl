; error: contradicts what is open
; The non-contradicting open demands the assertion hold: after Refl has equated C with D, m lists one
; constructor twice, and open-adt is refused (tests/open_absurd.sl is the form that fits there).

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m) (erased (Eq (T) (C) (D)) p) -> (many (Nat) n)
  (match erased p (((Nat) r))
    ((Refl A x) (open-adt erased m) (Zero))))
f
