; error: the `Matchable` for `T` is erased, so `comptime-match` cannot consult it
; A Matchable bound and opened at erased is Settled but holds only the token, so comptime-match cannot read it.
(def-fns _ $ (many mk : -> (erased (TyCtor -> Type) T)
    (many (ValCtor -> (T)) C) (many (ValCtor -> (T)) D)
    (many (Matchable enum T (many C) (many D)) m))
  (def-adts $ (U : -> Type) enum (many MkU : -> (U)) (many MkV : -> (U)))
  (values U MkU MkV (matchable-of U)))
(let ((erased T) (many C) (many D) (erased m)) (mk))
(open-adt erased m)
(let ((many v)) (D))
(comptime-match many v (D))
v
