; error: `c` is not a value constructor
; An entry whose type is not yet known to be a value-constructor type is
; refused by the Matchable former: otherwise this match, with no branch, would
; treat T as empty, and the call below, which passes the real MkOne, would
; give an erased False (section 24).

(def-adts $ (One : -> Type) enum (many MkOne : -> (One)))
(def-fns _ $ (many f : (erased (TyCtor -> Type) T) (erased Type A) (erased A c)
    (erased (Matchable enum T (many c)) m) (erased (T) x) -> (erased (False) n))
  (open-adt erased m)
  (match erased x (((False) r))))
(let ((erased bad)) (f One (ValCtor -> (One)) MkOne (matchable-of One) (MkOne)))
(Zero)
