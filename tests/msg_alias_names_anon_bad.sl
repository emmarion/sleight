; error: `c2` is not a constructor of `T1`
; A call's results are anonymous entries; a message names one by a let binder in scope equal to it.
(def-fns _ $ (many mk : (erased Type X) -> (erased (TyCtor -> Type) T) (many (ValCtor (many X v) -> (T)) c)
    (many (Matchable enum T (many c)) m))
  (def-adts $ (Foo : -> Type) enum (many FC : (many X v) -> (Foo)))
  (values Foo FC (matchable-of Foo)))
(let ((erased T1) (many c1) (many m1)) (mk (Nat)))
(let ((erased T2) (many c2) (many m2)) (mk (Nat)))
(open-adt many m1)
(open-adt many m2)
(let ((many w1)) (c1 0))
(comptime-match many w1 (c2 n))
(Zero)
