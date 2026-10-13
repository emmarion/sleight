; a Matchable lists the constructors in declared order
(def-adts $ (Two : -> Type) enum (many A : -> (Two)) (many B : (many (Nat) pred) -> (Two)))
(def-fns _ $ (many hold : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor (many (Nat) pred) -> (T)) D)
    (many (Matchable enum T (many D) (many C)) m) -> (many (Nat) n))
  0)
(hold Two A B (matchable-of Two))
