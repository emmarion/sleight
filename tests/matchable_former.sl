; expect: 0
; The Matchable former takes an entry whose type is a value-constructor type
; against the facts in force, including a forced one, and counts a mark
; written twice once (section 24).

(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased Type A) (erased A c)
    (erased (Eq Type A (ValCtor -> (T))) e) -> (many (Nat) n))
  (let-match erased e (Refl _ _))
  (def-fns _ $ (many _ : (erased (Matchable enum T (many c)) m) (erased (T) x) -> (many (Nat) r))
    (open-adt erased m)
    (match erased x (((Nat) r)) ((c) (Zero))))
  (Zero))

(def-fns X $ (many h : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C)
    (erased (Matchable enum newtype newtype T (many C)) m) -> (many (Nat) n))
  (open-adt erased m)
  (Zero))

(Zero)
