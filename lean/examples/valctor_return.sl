; a ValCtor whose return is headed by a type constructor from an enclosing former
(def-adts
  ((Box : (Type A) -> Type)
    enum
    (many MkBox : (erased Type A) (many A x) -> (Box A))))
(def-lvl L)
(def-fns L $ (many mk : (erased (TyCtor (Type A) -> Type) F) (many (ValCtor (erased Type B) (many B y) -> (F B)) c) (many (Nat) n) -> (many (F (Nat)) r))
  (c (Nat) n))
(mk Box MkBox (Succ (Zero)))
