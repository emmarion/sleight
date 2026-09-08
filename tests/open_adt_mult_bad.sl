; error: used in a non-erased position
; An erased Matchable cannot be opened at many, as it could not be let-bound at many.

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C)
    (erased (Matchable enum T (many C)) m) -> (many (Nat) n)
  (open-adt many m)
  (Zero))
f
