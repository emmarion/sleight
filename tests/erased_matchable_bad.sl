; error: Matchable for T is erased
; A non-erased match on a non-erased scrutinee reads its Matchable when the code runs, that being where an
; extern type's destructuring lives (section 41), so an erased one cannot serve.

(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(def-lvl X)
(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (match many x (((Nat) r))
    ((C n) n)))

(open Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
