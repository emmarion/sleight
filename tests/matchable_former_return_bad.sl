; error: `C` must return an application of `T`
; A Matchable entry must return an application of the Matchable's type
; constructor where the type is written, as a def-adts constructor must, so
; an entry returning the separate parameter U is refused even though this
; caller passes the same type for both (section 24).

(def-adts $ (One : -> Type) enum (many MkOne : -> (One)))
(def-fns _ $ (many f : (erased (TyCtor -> Type) T) (erased (TyCtor -> Type) U) (erased (ValCtor -> (U)) C)
    (erased (Matchable enum T (many C)) m) (erased (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (match erased x (((Nat) r)) ((C) 7)))
(f One One MkOne (matchable-of One) (MkOne))
