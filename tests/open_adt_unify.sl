; expect: (A)
; Opening a Matchable unifies it with every opened one that lists one of its constructors or heads its type
; constructor, minting the facts that takes (proposals/matchable-newtype-opening.md): m1 and m2 share C, so
; opening both equates T with U and D with E, and a (T) value is returned where a (U) is declared.

(def-adts $ Two : -> Type enum (many A : -> (Two)) (many B : -> (Two)))
(def-lvl X)
(def-fns X $ many cast : (erased (TyCtor -> Type) T) (erased (TyCtor -> Type) U)
    (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D) (erased (ValCtor -> (U)) E)
    (erased (Matchable enum T (many C) (many D)) m1)
    (erased (Matchable enum U (many C) (many E)) m2)
    (many (T) x) -> (many (U) y)
  (open-adt m1)
  (open-adt m2)
  x)
(cast Two Two A B B (matchable-of Two) (matchable-of Two) (A))
