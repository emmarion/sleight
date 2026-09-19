; error: contradicts what is open

(def-adts $ U : -> Type
  union newtype
  (many W : (many (Nat) n) -> (U))
  (erased G : (erased (Nat) n) -> (U)))

(def-lvl X)
(def-fns X $ many through : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) D)
    (many (ValCtor (erased (Nat) n) -> (T)) C)
    (erased (Matchable union newtype T (many D) (erased C)) m)
    (erased (T) x) -> (erased (Nat) r)
  (open-adt erased m)
  (match erased x (((Nat) r)) ((D n) n) ((C n) n)))

(let (erased r) (through U W G (matchable-of U) (G (Zero))))

(def-fns X $ many coexist : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (erased C)) m)
    (erased (Matchable enum newtype T (many C)) nt) -> (many (Nat) r)
  (open-adt erased m)
  (open-adt erased nt)
  (Zero))

coexist
