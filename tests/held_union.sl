; expect: 1
(def-adts $ U : -> Type union
  (many UA : (erased (Nat) n) -> (U))
  (many UB : (many (Nat) n) -> (U)))
(def-lvl X)
(def-fns X $ many g : (erased (TyCtor -> Type) T)
    (erased (ValCtor (erased (Nat) n) -> (T)) C)
    (erased (ValCtor (many (Nat) n) -> (T)) D)
    (many (Matchable union T (many C) (many D)) m)
    (erased (Nat) k) (many (D k) is x) -> (many (Nat) n)
  (open-adt many m)
  (match many x (((Nat) r))
    (absurd C)
    ((D n) n)))
(def-lvl Y)
(let (erased xy) (prove-predates X Y))
(def-fns Y $ many go : -> (many (Nat) n) (g (predates xy) U UA UB (matchable-of U) (Succ (Zero)) (UB (Succ (Zero)))))
go
