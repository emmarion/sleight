; expect: (Succ (Zero))
; Of two consistent first-class Matchables for one type, a non-erased match reads the non-erased one (section 19),
; whichever was bound later.
(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m1)
    (erased (Matchable enum T (many C)) m2)
    (many (T) x) -> (many (Nat) n)
  (match many x (((Nat) r)) ((C n) n)))
(open Box MkBox (matchable-of Box) (matchable-of Box) (MkBox (Succ (Zero))))
