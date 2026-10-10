; error: `k` is not a value constructor
; A match naming a Matchable entry that is not a constructor is refused (section 24).

(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased (Nat) k)
    (erased (Matchable enum T (many k)) m) (erased (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (match erased x (((Nat) r)) ((k) (Zero))))
