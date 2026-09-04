; error: branch D is refuted
; The same disjointness makes a present D branch an error where the scrutinee is C-headed, as it would be for
; the constructors def-adts minted.
(def-adts $ Two : -> Type enum
  (many A : (many (Nat) n) -> (Two))
  (many B : (many (Nat) n) -> (Two)))
(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (ValCtor (many (Nat) n) -> (T)) D)
    (many (Matchable enum T (many C) (many D)) m)
    (erased (Nat) k) -> (many (Nat) n)
  (match erased (C k) (((Nat) r))
    ((C n) (Zero))
    ((D n) (Succ (Zero)))))
(f Two A B (matchable-of Two) (Zero))
