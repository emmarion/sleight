; a Matchable (DESIGN.md section 24) as a value: its type names a declared type and its constructors in order
(def-adts $ (Two : -> Type) enum (many A : -> (Two)) (many B : (many (Nat) pred) -> (Two)))
(def-fns _ $ (many hold : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor (many (Nat) pred) -> (T)) D)
    (many (Matchable enum T (many C) (many D)) m) -> (many (Nat) n))
  0)
(hold Two A B (matchable-of Two))
