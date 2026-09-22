; expect: 1
; Two constructors one Matchable lists are distinct even as first-class parameters of equal arity (sections 18, 19):
; with x known to be C-headed, the D branch of a union match is refuted, which is what lets the match be written.
(def-adts $ (U : -> Type) union
  (many UA : (many (Nat) n) -> (U))
  (many UB : (erased (Nat) n) -> (U)))
(def-lvl X)
(def-fns X $ (many g : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (ValCtor (erased (Nat) n) -> (T)) D)
    (many (Matchable union T (many C) (many D)) m)
    (erased (Nat) k) (many (C k) is x) -> (many (Nat) n))
  (open-adt many m)
  (match many x (((Nat) r))
    ((C n) n)
    (absurd D)))
(def-lvl Y)
(let ((erased xy)) (prove-predates X Y))
(def-fns Y $ (many go : -> (many (Nat) n)) (g (predates xy) U UA UB (matchable-of U) (Succ (Zero)) (UA (Succ (Zero)))))
go
