(def-fns _ $ (erased use : (erased (TyCtor ((Nat) a) -> Type) R)
    (erased (ValCtor (erased (Nat) n) -> (R (Succ n))) C)
    (erased (Matchable enum R (many C)) mt)
    (erased (Nat) a) (erased (R a) d) -> (erased (Nat) r))
  (open-adt erased mt)
  (let-match erased d (C n))
  n)
(def-adts $ (Pz : ((Nat) a) -> Type)
  enum
  (many MkPos1 : (erased (Nat) n) -> (Pz (Succ n))))
(let ((erased r)) (use Pz MkPos1 (matchable-of Pz) (Succ 2) (MkPos1 2)))
0
