; A type whose def-adts mentions a top-level entry, and its constructor, passed as values
(let ((erased N)) (Nat))
(def-adts ((Box : -> Type) enum (many MkBox : (many N n) -> (Box))))
(def-fns _ $ (many build : (erased (TyCtor -> Type) T) (many (ValCtor (many (Nat) n) -> (T)) K) (many (Nat) x)
    -> (many (T) y))
  (K x))
(def-fns _ $ (many get : (many (Box) b) -> (many (Nat) r))
  (match many b (((Nat) r)) ((MkBox n) n)))
(get (build Box MkBox 3))
