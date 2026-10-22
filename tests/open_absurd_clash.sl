; The contradiction between two opened Matchables that name one type constructor but cannot unify is what
; open-absurd cashes in (DESIGN.md section 8), here as a whole function body.

(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m1)
    (erased (Matchable enum T (many C)) m2) -> (many (Nat) n))
  (open-adt erased m1)
  (open-absurd m2 _))
