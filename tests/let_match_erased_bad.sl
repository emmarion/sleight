; error: Matchable for T is erased
; let-match is a match: outside run position, at many, it dispatches at runtime through its Matchable, so an
; erased opened one is refused as it is for match (ASSUMPTIONS 142). Accepted, this compiled to code reading
; the erased m and failed when run.

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ (many peel : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (let-match many x (C n))
  n)
(peel Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
