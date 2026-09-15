; expect: (Succ (Zero))
; coercible-ctor reads no Matchable, so it needs none opened and refuses no phantom constructor: a coerce
; cashes its proof only for a non-erased source, which no phantom constructor heads (sections 20, 38; the
; owner's decision in chat, ASSUMPTIONS 141). The first proof is built through a first-class C with no
; Matchable in sight; the second relates two Ghost-headed values, and no coerce could use it.

(def-adts $ T : -> Type
  enum
  (many MkT : (many (Nat) n) -> (T))
  (erased Ghost : (erased (Nat) n) -> (T)))
(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) U) (erased (ValCtor (many (Nat) n) -> (U)) C) (many (Nat) n) -> (many (Nat) r)
  (let (erased p) (coercible-ctor C (coercible-refl n)))
  (let (erased q) (coercible-ctor Ghost (Zero) n))
  (Succ n))
(f T MkT (Zero))
