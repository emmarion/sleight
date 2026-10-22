; expect: 1
; coercible-ctor reads no Matchable and refuses no phantom constructor (section 33 item 6). The first proof
; is built through a first-class C with no Matchable in sight; the second relates two Ghost-headed values.

(def-adts $ (T : -> Type)
  enum
  (many MkT : (many (Nat) n) -> (T))
  (erased Ghost : (erased (Nat) n) -> (T)))
(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) U) (erased (ValCtor (many (Nat) n) -> (U)) C) (many (Nat) n) -> (many (Nat) r))
  (let ((erased _)) (coercible-ctor (Shared) C (coercible-refl (Shared) n)))
  (let ((erased _)) (coercible-ctor (Shared) Ghost (Zero) n))
  (Succ n))
(f T MkT (Zero))
