; error: `Matchable` for `T` is erased
; The marker is the opened entry's multiplicity: a many parameter opened at erased serves no match that
; dispatches at runtime (DESIGN.md section 19, ASSUMPTIONS 139).

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (match many x (((Nat) r)) ((C n) n)))
(open Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
