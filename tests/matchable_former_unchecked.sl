; expect: 0
; The Matchable former checks nothing beyond its shape: entries that are not
; constructors, and a mark twice, are accepted and may be opened (section 24).

(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased (Nat) k)
    (erased (Matchable enum T (many k) (many 3)) m) -> (many (Nat) n))
  (open-adt erased m)
  (Zero))

(def-fns X $ (erased g : (erased (TyCtor -> Type) T) (erased (Nat) a) (erased (Nat) b)
    (erased (Matchable enum T (many a) (many b)) m) (erased (Eq (Nat) a b) e) ->
    (erased (False) r))
  (open-adt erased m)
  (match erased e _))

(def-fns X $ (many h : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C)
    (erased (Matchable enum newtype newtype T (many C)) m) -> (many (Nat) n))
  (open-adt erased m)
  (Zero))

(Zero)
